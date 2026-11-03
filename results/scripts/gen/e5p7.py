"""E5 at p = 7 by hand: modular symbols for eq. (closed) with k = 5, and S_7."""
from sage.all__sagemath_schemes import EllipticCurve, QQ, pari
from math import comb
E = EllipticCurve([0,0,1,-79,342]); p = 7; k = 5
f = E.modular_symbol(sign=+1, implementation='num')
ap = int(E.ap(p)); print('ap', ap, 'cinf', E.real_components())
A = {a: f(QQ(a)/p) for a in range(1, p)}
print('[a/7]', A)
B = {}
for j in range(k, p):
    for a in range(1, p):
        b = pow(a, p, p*p) * pow(1+p, j, p*p) % (p*p)
        B[(a, j)] = (b, f(QQ(b)/p**2))
print('b_{a,j},[b/49]', B)
def red(q): q = QQ(q); return int(q.numerator()) * pow(int(q.denominator()), -1, p) % p
api = pow(ap % p, -1, p)
s = 0
for j in range(k, p):
    for a in range(1, p):
        s += comb(j, k) * (api**2 * red(B[(a, j)][1]) - api**3 * red(A[a]))
print('a5 mod 7 =', s % p)
pe = pari.ellinit([0,0,1,-79,342])
P = pari('[[-10,11],[-39/4,105/8],[-8,21],[-7,23],[-6,24]]')
R = pari.ellpadicregulator(pe, p, 6, P); L = pari('log(1+7+O(7^8))')
x = pari('x'); al = [z for z in pari.polrootspadic(x**2-ap*x+p, p, 8) if pari.valuation(z, p) == 0][0]
S = (1-1/al)**2 * R / L**5
print('Reg_7', R, ' alpha', al, ' S_7', S)
M = pari.ellpadicheightmatrix(pe, p, 4, P); s2 = pari.ellpadics2(pe, p, 4)
print('heights', M[0]-s2*M[1])
for q in (2,3): print(q, E.ap(q), pari.ellcard(pe, q) if hasattr(pari,'ellcard') else '')
