"""Riemann sum a_{n,k} of the p-adic L-function of an ordinary curve, directly from
modular symbols: a_{n,k} = sum_j C(j,k) sum_a mu(omega(a)(1+p)^j + p^n Z_p).
Usage: fastsum.py "a1,a2,a3,a4,a6" p n k nproc  -> prints a_{n,k} mod p^(n-1) for k=1..kmax"""
import sys, time
from multiprocessing import Pool
from sage.all__sagemath_schemes import EllipticCurve, QQ
import sage.all__sagemath_eclib  # noqa

ai = [int(x) for x in sys.argv[1].split(',')]
p, n, kmax, nproc = (int(x) for x in sys.argv[2:6])
E = EllipticCurve(ai)
K = n + 3
MOD = p ** K
f = E.modular_symbol(sign=+1, implementation='eclib')

def red(q):
    q = QQ(q)
    return int(q.numerator()) * pow(int(q.denominator()), -1, MOD) % MOD

ap = int(E.ap(p))
al = next(x for x in range(1, p) if (x * x - ap * x + p) % p == 0)
for _ in range(2 * K):  # Newton for the unit root of x^2 - ap x + p
    al = (al - (al * al - ap * al + p) * pow(2 * al - ap, -1, MOD)) % MOD
ainv = pow(al, -1, MOD)
c1 = pow(ainv, n, MOD); c2 = pow(ainv, n + 1, MOD)
pn, pn1 = p ** n, p ** (n - 1)
omega = [0] + [pow(a, pn1, pn) for a in range(1, p)]
half = (p - 1) // 2
low = {}

def lowval(c):
    v = low.get(c)
    if v is None:
        v = red(f(QQ(c) / pn1)); low[c] = v
    return v

def block(js):
    j0, j1 = js
    out = []
    g = pow(1 + p, j0, pn)
    for j in range(j0, j1):
        s = 0
        for a in range(1, half + 1):
            b = omega[a] * g % pn
            s += c1 * red(f(QQ(b) / pn)) - c2 * lowval(b % pn1)
        out.append(2 * s % MOD)   # a and p-a give the same value since f(-r)=f(r)
        g = g * (1 + p) % pn
    return j0, out

if __name__ == '__main__':
    t = time.time()
    J = pn1
    step = max(1, J // (nproc * 40))
    chunks = [(i, min(i + step, J)) for i in range(0, J, step)]
    M = [0] * J
    with Pool(nproc) as P:
        for j0, out in P.imap_unordered(block, chunks):
            M[j0:j0 + len(out)] = out
    res = []
    for k in range(1, kmax + 1):
        s = 0; c = 0  # C(j,k) iteratively
        from math import comb
        for j in range(J):
            if j >= k:
                s += comb(j, k) * M[j]
        res.append(s % (p ** (n - 1)))
    print(dict(p=p, n=n, ap=ap, coeffs=res, prec=n - 1, sec=round(time.time() - t, 1)), flush=True)
