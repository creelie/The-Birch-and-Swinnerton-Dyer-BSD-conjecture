"""Certify Sha(E/Q)[p] = 0 for given curves and primes (Stein--Wuthrich method, see shacert.py).

Usage: python3 certify.py OUT.jsonl PMAX  < curves.txt
curves.txt lines (Cremona allgens format): N class num [a1,a2,a3,a4,a6] r [tors gens] [gens...]

For each good ordinary prime 5 <= p < PMAX it records:
  surj   Frobenius witnesses (q1,q2,q3) proving rho_{E,p} surjective, or null
  ar     coefficient of T^r of L_p(E,T) mod p (Sage padic_lseries, eclib modular symbols, level 2)
  low    the coefficients of T^0..T^{r-1} mod p (must be 0)
  vS     valuation of (1-1/alpha)^2 prod c_v Reg_gamma / tors^2 (PARI p-adic regulator)
  status certified | irregular | not-surjective | error
"""
import json
import os
import sys
import time

# 'eclib' (exact modular symbols) or 'num' (Wuthrich's numerical modular symbols with proven
# rounding, valid when the Manin constant is 1, e.g. for semistable optimal curves)
IMPL = os.environ.get('CERT_IMPL', 'eclib')

from sage.all__sagemath_schemes import EllipticCurve, QQ, ZZ, primes, pari as spari
import sage.all__sagemath_eclib  # noqa: F401  (loads eclib backend)


def parse(line):
    t = line.split()
    N, cl, num = int(t[0]), t[1], int(t[2])
    ai = [int(x) for x in t[3].strip('[]').split(',')]
    r = int(t[4])
    pts = []
    for g in t[6:6 + r]:  # the r Mordell-Weil generators come first, torsion generators after
        x, y, z = [int(u) for u in g.strip('[]').split(':')]
        pts.append((QQ(x) / z, QQ(y) / z))
    return f"{N}{cl}{num}", ai, r, pts


def surjective_certificate(ap_of, N, p, qmax=50000):
    need = [None, None, None]
    for q in primes(2, qmax):
        if None not in need:
            break
        if N % q == 0 or q == p:
            continue
        a = ap_of(q) % p
        if a == 0:
            continue
        d = (a * a - 4 * q) % p
        if d:
            sq = pow(d, (p - 1) // 2, p) == 1
            if not sq and need[0] is None:
                need[0] = int(q)
            if sq and need[1] is None:
                need[1] = int(q)
        u = a * a * pow(int(q), -1, p) % p
        if u not in (0, 1, 2, 4) and (u * u - 3 * u + 1) % p and need[2] is None:
            need[2] = int(q)
    return need if None not in need else None


def run(label, ai, r, pts, pmax, out):
    E = EllipticCurve(ai)
    assert E.is_minimal() if hasattr(E, 'is_minimal') else True
    N = int(E.conductor())
    if E.has_cm():
        out.write(json.dumps(dict(curve=label, status='cm')) + '\n')
        return
    t0 = time.time()
    aps = {}
    ap_list = E.aplist(50000)
    for q, a in zip(primes(50000), ap_list):
        aps[int(q)] = int(a)
    tam = int(E.tamagawa_product())
    tors = int(E.torsion_order())
    pe = spari(ai)
    pe = spari.ellinit(pe)
    gens = spari([[P[0], P[1]] for P in pts])
    # check the points lie on E and are independent (nonzero real regulator)
    for P in pts:
        assert E.is_on_curve(P[0], P[1])
    reg_real = spari.ellheightmatrix(pe, gens).matdet()
    assert abs(float(reg_real)) > 1e-8 and len(pts) == r
    init = time.time() - t0
    plist = [int(x) for x in os.environ['CERT_PRIMES'].split(',')] if os.environ.get('CERT_PRIMES') else [int(x) for x in primes(5, pmax)]
    for p in plist:
        if N % p == 0:
            continue
        ap = aps[p] if p in aps else int(E.ap(p))
        if ap % p == 0:
            continue  # supersingular (a_p = 0 for p >= 5)
        rec = dict(curve=label, N=N, r=r, p=p, ap=ap)
        t = time.time()
        try:
            surj = surjective_certificate(lambda q: aps[int(q)] if int(q) in aps else int(E.ap(q)), N, p)
            rec['surj'] = surj
            if surj is None:
                rec['status'] = 'not-surjective'
                out.write(json.dumps(rec) + '\n')
                continue
            L = E.padic_lseries(p, implementation=IMPL)
            s = L.series(2, prec=r + 2)
            co = [s[i] for i in range(r + 1)]
            low = [int(ZZ(c.lift()) % p) if c.precision_absolute() >= 1 else None for c in co[:r]]
            ar = co[r]
            rec['low'] = low
            ap_abs = ar.precision_absolute()
            rec['ar_prec'] = int(min(ap_abs, 10**6))
            rec['ar'] = int(ZZ(ar.lift()) % p) if ap_abs >= 1 else None
            # p-adic BSD quantity S
            R = spari.ellpadicregulator(pe, p, 12, gens)
            lg = spari(f'log(1+{p}+O({p}^14))')
            al = spari(f'polrootspadic(x^2-({ap})*x+{p},{p},14)')
            al = [a for a in al if spari.valuation(a, p) == 0][0]
            S = (1 - 1 / al) ** 2 * tam * R / lg ** r / tors ** 2
            vS = int(spari.valuation(S, p))
            rec['vS'] = vS
            rec['vReg'] = int(spari.valuation(R, p))
            if vS == 0 and rec['ar'] not in (None, 0) and all(x == 0 for x in low):
                rec['status'] = 'certified'
                # conjectural #Sha mod p (sanity): a_r / S, up to the normalising unit -1/2 of Sage
                u = spari(f'Mod({rec["ar"]},{p})') / spari(f'Mod({int(spari.truncate(S))},{p})')
                rec['ratio'] = int(spari.lift(u))
            elif vS > 0 or rec['ar'] == 0:
                rec['status'] = 'irregular'   # settle with refine.py at a higher level
            else:
                rec['status'] = 'undecided'
        except Exception as e:  # record, never hide
            rec['status'] = 'error'
            rec['err'] = repr(e)[:300]
        rec['sec'] = round(time.time() - t, 3)
        out.write(json.dumps(rec) + '\n')
        out.flush()
    out.write(json.dumps(dict(curve=label, done=True, init=round(init, 1),
                              total=round(time.time() - t0, 1))) + '\n')
    out.flush()


if __name__ == '__main__':
    outp, pmax = sys.argv[1], int(sys.argv[2])
    import os
    done = set()
    if os.path.exists(outp):
        for l in open(outp):
            try:
                d = json.loads(l)
            except ValueError:
                continue
            if d.get('done') or d.get('status') == 'cm':
                done.add(d['curve'])
    with open(outp, 'a') as out:
        for line in sys.stdin:
            if line.strip():
                lab, ai, r, pts = parse(line)
                if lab in done:
                    continue
                try:
                    run(lab, ai, r, pts, pmax, out)
                except Exception as e:  # record and go on
                    out.write(json.dumps(dict(curve=lab, status='curve-error', err=repr(e)[:300])) + '\n')
                    out.flush()
