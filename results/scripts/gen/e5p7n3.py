"""E5 at p = 7: a_0..a_5 modulo 7^2 from the Riemann sum of level 3 (Prop. leveln)."""
from sage.all__sagemath_schemes import EllipticCurve, QQ
from math import comb
E = EllipticCurve([0,0,1,-79,342]); p = 7; n = 3; MOD = p**(n-1); K = p**(n+3)
f = E.modular_symbol(sign=+1, implementation='num')
ap = int(E.ap(p))
al = next(x for x in range(1, p) if (x*x - ap*x + p) % p == 0)
for _ in range(40): al = (al - (al*al - ap*al + p) * pow(2*al - ap, -1, K)) % K
ai = pow(al, -1, K)
def red(q): q = QQ(q); return int(q.numerator()) * pow(int(q.denominator()), -1, K) % K
pn, pn1 = p**n, p**(n-1)
cache = {}
def sym(num, den):
    key = (num % den, den)
    if key not in cache: cache[key] = f(QQ(num)/den)
    return cache[key]
coef = [0]*7
for j in range(pn1):
    for a in range(1, (p+1)//2):
        b = pow(a, pn1, pn) * pow(1+p, j, pn) % pn
        m = pow(ai, n, K) * red(sym(b, pn)) - pow(ai, n+1, K) * red(sym(b, pn1))
        for k in range(0, 6):
            coef[k] += 2 * comb(j, k) * m
print([c % MOD for c in coef[:6]], 'symbols', len(cache))
