"""Second pass for pairs (E, p) not settled at level 2: compute L_p at level n (coefficients mod p^(n-1))
and compare v(a_r) with v(S).  Usage: python3 refine.py OUT.jsonl N < pairs.txt
pairs.txt lines: <allgens line> | p"""
import json, os, sys, time
from sage.all__sagemath_schemes import EllipticCurve, QQ, ZZ, pari as spari
import sage.all__sagemath_eclib  # noqa
from certify import parse

def vS_of(ai, pts, p, r, E):
    pe = spari.ellinit(spari(ai)); gens = spari([[P[0], P[1]] for P in pts])
    ap = int(E.ap(p))
    R = spari.ellpadicregulator(pe, p, 14, gens)
    lg = spari(f'log(1+{p}+O({p}^16))')
    al = [a for a in spari(f'polrootspadic(x^2-({ap})*x+{p},{p},16)') if spari.valuation(a, p) == 0][0]
    S = (1 - 1 / al) ** 2 * int(E.tamagawa_product()) * R / lg ** r / int(E.torsion_order()) ** 2
    return int(spari.valuation(S, p))

def main():
    outp, n = sys.argv[1], int(sys.argv[2])
    cache = {}
    with open(outp, 'a') as out:
        for line in sys.stdin:
            if not line.strip():
                continue
            g, p = line.rsplit('|', 1); p = int(p)
            lab, ai, r, pts = parse(g)
            if lab not in cache:
                cache.clear(); cache[lab] = EllipticCurve(ai)
            E = cache[lab]; t = time.time()
            vS = vS_of(ai, pts, p, r, E)
            s = E.padic_lseries(p, implementation=os.environ.get('CERT_IMPL', 'eclib')).series(n, prec=r + 2)
            co = [s[i] for i in range(r + 1)]
            ar = co[r]; prec = int(min(ar.precision_absolute(), 10**6))
            v = int(ar.valuation()) if ar != 0 else None   # None: zero to the known precision
            rec = dict(curve=lab, p=p, r=r, n=n, vS=vS, ar_val=v, ar_prec=prec,
                       low_prec=[int(min(c.precision_absolute(), 10**6)) for c in co[:r]],
                       ar=str(ar))
            if v is not None and v < prec and v == vS:
                rec['status'] = 'certified'
            elif v is not None and v < prec:
                rec['status'] = 'bound'          # v(#Sha[p^oo]) <= v - vS
                rec['sha_bound'] = v - vS
            else:
                rec['status'] = 'undecided'
            rec['sec'] = round(time.time() - t, 1)
            out.write(json.dumps(rec) + '\n'); out.flush()

if __name__ == '__main__':
    main()
