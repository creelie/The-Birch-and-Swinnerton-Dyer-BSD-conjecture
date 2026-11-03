"""Certify Sha(E/Q)[p] = 0 for an elliptic curve of rank r >= 2 and a good ordinary prime p.

Method (Stein--Wuthrich, Math. Comp. 82 (2013), Algorithm 11.1 and Section 12.4):

* Kato: if p >= 5 is a good prime and rho_{E,p} is surjective, the characteristic series f_E(T)
  of the dual Selmer group over the cyclotomic Z_p-extension divides L_p(E,T) in Z_p[[T]].
* Schneider / Perrin-Riou: ord_T f_E >= r, with equality iff the p-adic regulator is nonzero
  and Sha(E/Q)[p^oo] is finite; then the leading coefficient of f_E has the valuation of
  (1-1/alpha)^2 * prod c_v * #Sha[p^oo] * Reg_gamma / #E(Q)_tors^2.

So if the coefficient a_r of T^r in L_p(E,T) satisfies v(a_r) = v(S), with
S = (1-1/alpha)^2 prod c_v Reg_gamma / tors^2, then ord_T L_p = r (the lower coefficients vanish
by the two theorems), hence ord_T f_E = r, Sha[p^oo] is finite and v(#Sha[p^oo]) <= v(a_r) - v(S) = 0.

L_p(E,T) is approximated by the Riemann sum P_2(T) of the Mazur--Tate--Teitelbaum measure built
from the plus modular symbol of E (exact rationals from PARI's msfromell / mseval).  By
Stein--Wuthrich Prop. 3.5, the coefficient of T^j in P_2 agrees with that of L_p modulo
p^(1 - c) for 1 <= j < p, where p^c clears the denominators of P_1, P_2; c = 0 is checked.
"""
import cypari2

pari = cypari2.Pari()
pari.allocatemem(6 * 10**9, silent=True) if 'silent' in pari.allocatemem.__doc__ else None
OO = pari('oo')


def unit_root(ap, p, K):
    """Unit root alpha of X^2 - ap X + p in Z/p^K (Hensel from alpha = ap mod p)."""
    mod = p**K
    a = ap % p
    for _ in range(K + 2):
        f = (a * a - ap * a + p) % mod
        df = (2 * a - ap) % mod
        a = (a - f * pow(df, -1, mod)) % mod
    assert (a * a - ap * a + p) % mod == 0
    return a


class Symbols:
    """Plus modular symbol r -> [r]^+ of E, with [0]^+ = L(E,1)/Omega^+."""

    def __init__(self, E):
        self.M, self.x = pari.msfromell(E, 1)
        self.cache = {}
        # orientation: PARI path [a,b]; fix the sign so that [0]^+ = L(E,1)/Omega^+
        self.sign = 1

    def __call__(self, num, den):
        num %= den
        key = (num, den)
        v = self.cache.get(key)
        if v is None:
            v = pari.mseval(self.M, self.x, [pari(num) / den, OO])
            self.cache[key] = v
        return v


def p2_coeffs(sym, p, ap, rmax=5, K=4):
    """Coefficients of T^0..T^rmax of P_2(T), as integers mod p^K, plus the denominator test.

    mu(b + p^2 Z_p) = alpha^-2 [b/p^2]^+ - alpha^-3 [b/p]^+.
    P_2(T) = sum_{a=1}^{p-1} sum_{j=0}^{p-1} mu(omega(a)(1+p)^j + p^2 Z_p) (1+T)^j.
    """
    mod = p**K
    alpha = unit_root(ap, p, K + 2)
    ia = pow(alpha, -1, mod)
    ia2, ia3 = ia * ia % mod, ia * ia * ia % mod
    p2 = p * p
    # level-1 symbols [b/p], level-2 symbols [b/p^2]; record denominators
    den_bad = False
    s1 = {}
    for b in range(1, p):
        v = sym(b, p)
        d = int(pari.denominator(v))
        if d % p == 0:
            den_bad = True
        s1[b] = int(pari.numerator(v)) * pow(d, -1, mod) % mod if d % p else 0
    c = [0] * p  # c[j] = sum_a mu(omega(a)(1+p)^j)
    g = 1
    gpow = [1] * p
    for j in range(1, p):
        gpow[j] = gpow[j - 1] * (1 + p) % p2
    for a in range(1, p):
        w = pow(a, p, p2)  # Teichmueller lift mod p^2
        for j in range(p):
            b = w * gpow[j] % p2
            v = sym(b, p2)
            d = int(pari.denominator(v))
            if d % p == 0:
                den_bad = True
                continue
            x2 = int(pari.numerator(v)) * pow(d, -1, mod) % mod
            c[j] = (c[j] + ia2 * x2 - ia3 * s1[b % p]) % mod
    # coefficients of T^i: sum_j c_j binom(j, i)
    coeffs = []
    for i in range(rmax + 1):
        s = 0
        for j in range(i, p):
            s += c[j] * _binom(j, i)
        coeffs.append(s % mod)
    return coeffs, den_bad, alpha


_bc = {}


def _binom(n, k):
    key = (n, k)
    v = _bc.get(key)
    if v is None:
        from math import comb
        v = comb(n, k)
        _bc[key] = v
    return v


def vp(x, p):
    x = int(x)
    if x == 0:
        return 10**9
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def surjective_certificate(E, p, N, qmax=20000):
    """Prove rho_{E,p} surjective (p >= 5, E without CM) from Frobenius traces.

    A proper subgroup G of GL_2(F_p) with surjective determinant and not containing SL_2 lies in
    a Borel subgroup, the normaliser of a split or non-split Cartan subgroup, or has projective
    image A_4, S_4 or A_5 (Dickson; Serre, Invent. Math. 15 (1972), Section 2).  For Frob_q:
      * q1 with a_q != 0 and a_q^2 - 4q a non-square mod p: not in a Borel (reducible char. poly.),
        not in a split Cartan (split), not in its normaliser minus the Cartan (trace 0);
      * q2 with a_q != 0 and a_q^2 - 4q a non-zero square: not in a non-split Cartan (irreducible
        or scalar char. poly.), not in its normaliser minus the Cartan (trace 0);
      * q3 with u = a_q^2/q not in {0, 1, 2, 4} and u^2 - 3u + 1 != 0 mod p: projective order > 5,
        so not in A_4, S_4, A_5.
    Returns the triple (q1, q2, q3) or None.
    """
    need = [None, None, None]
    q = 2
    while q < qmax and None in need:
        q = int(pari.nextprime(q + 1))
        if N % q == 0 or q == p:
            continue
        a = int(pari.ellap(E, q)) % p
        if a == 0:
            continue
        d = (a * a - 4 * q) % p
        if d != 0:
            sq = pow(d, (p - 1) // 2, p) == 1
            if not sq and need[0] is None:
                need[0] = q
            if sq and need[1] is None:
                need[1] = q
        u = a * a * pow(q, -1, p) % p
        if u not in (0, 1, 2, 4) and (u * u - 3 * u + 1) % p and need[2] is None:
            need[2] = q
    return tuple(need) if None not in need else None
