"""For the rank-three pairs with p in PS: a_3 modulo p^(v+2) from the Riemann sum of level v+3,
and S_p modulo p^(v+2); records whether a_3 = S_p modulo p^(v+2).  Usage: deep2.py OUT.jsonl nproc"""
import sys, json, gzip, time
from multiprocessing import Pool
from math import comb
PS = (5, 7, 11, 13)

def work(job):
    from sage.all__sagemath_schemes import EllipticCurve, QQ, pari
    import sage.all__sagemath_eclib  # noqa
    lab, ai, pts, plist = job
    t0 = time.time()
    E = EllipticCurve(ai)
    f = E.modular_symbol(sign=+1, implementation='eclib')
    pe = pari.ellinit(ai)
    gens = [[pari(str(x)), pari(str(y))] for x, y in pts]
    tam = int(pari.ellglobalred(pe)[2]); tors = int(pari.elltors(pe)[0])
    cinf = int(E.real_components())  # [r]^+ is normalised by the Neron period c_inf * Omega_0
    out = []
    for p, v in plist:
        n = v + 3; K = n + 3; MOD = p ** K; pn, pn1 = p ** n, p ** (n - 1)
        def red(q):
            q = QQ(q); return int(q.numerator()) * pow(int(q.denominator()), -1, MOD) % MOD
        ap = int(E.ap(p))
        al = next(x for x in range(1, p) if (x * x - ap * x + p) % p == 0)
        for _ in range(2 * K):
            al = (al - (al * al - ap * al + p) * pow(2 * al - ap, -1, MOD)) % MOD
        ainv = pow(al, -1, MOD); c1 = pow(ainv, n, MOD); c2 = pow(ainv, n + 1, MOD)
        omega = [0] + [pow(a, pn1, pn) for a in range(1, p)]
        low = {}
        M = []
        g = 1
        for j in range(pn1):
            s = 0
            for a in range(1, (p - 1) // 2 + 1):
                b = omega[a] * g % pn
                c = b % pn1
                if c not in low: low[c] = red(f(QQ(c) / pn1))
                s += c1 * red(f(QQ(b) / pn)) - c2 * low[c]
            M.append(2 * s % MOD); g = g * (1 + p) % pn
        ci = pow(cinf, -1, MOD)
        a3 = ci * sum(comb(j, 3) * M[j] for j in range(3, pn1)) % (p ** (n - 1))
        lows = [ci * sum(comb(j, k) * M[j] for j in range(k, pn1)) % (p ** (n - 1)) for k in (0, 1, 2)]
        R = pari.ellpadicregulator(pe, p, v + 8, gens)
        lg = pari(f'log(1+{p}+O({p}^{v+10}))')
        alp = [x for x in pari(f'polrootspadic(x^2-({ap})*x+{p},{p},{v+10})') if pari.valuation(x, p) == 0][0]
        S = (1 - 1 / alp) ** 2 * tam * R / lg ** 3 / tors ** 2
        Sm = int(pari.lift(pari(f'Mod({pari.truncate(S/pari(p)**v)},{p**2})'))) * p ** v
        out.append(dict(curve=lab, p=p, v=v, n=n, a3=a3, S=Sm % p ** (v + 2), agree=(a3 - Sm) % p ** (v + 2) == 0,
                        low=lows, vS=int(pari.valuation(S, p))))
    return out, round(time.time() - t0, 1)

if __name__ == '__main__':
    cur = {}
    for l in open('rank3.txt'):
        t = l.split(); lab = t[0] + t[1] + t[2]
        pts = []
        for gg in t[6:9]:
            x, y, z = [int(u) for u in gg.strip('[]').split(':')]
            pts.append((f'{x}/{z}', f'{y}/{z}'))
        cur[lab] = ([int(x) for x in t[3].strip('[]').split(',')], pts)
    jobs = {}
    for l in gzip.open('rank3.jsonl.gz', 'rt'):
        x = json.loads(l)
        if x['p'] in PS: jobs.setdefault(x['curve'], []).append((x['p'], x.get('vS', 0)))
    done = set()
    try:
        for l in open(sys.argv[1]): done.add(json.loads(l)['curve'])
    except FileNotFoundError: pass
    J = [(c, cur[c][0], cur[c][1], pl) for c, pl in jobs.items() if c not in done]
    print(len(J), 'curves', flush=True)
    with open(sys.argv[1], 'a') as fo, Pool(int(sys.argv[2])) as P:
        for out, sec in P.imap_unordered(work, J):
            for r in out: fo.write(json.dumps(r) + '\n')
            fo.flush()
