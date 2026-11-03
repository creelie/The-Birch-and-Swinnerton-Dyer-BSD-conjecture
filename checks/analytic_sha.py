"""Numerical check of the Birch--Swinnerton-Dyer formula for sample curves.

For each curve this computes the analytic rank r, the leading coefficient
L^(r)(E,1)/r!, the real period, Tamagawa numbers, torsion, a basis of the
Mordell--Weil group (by 2-descent and saturation in PARI/GP) and its regulator,
and the "analytic order of Sha"

    Sha_an = (L^(r)(E,1)/r!) * #E(Q)_tors^2 / (Omega * Reg * prod c_p).

The conjecture predicts that Sha_an is the order of Sha, hence a square
integer. This is a numerical check, not a proof.

Requires: pip install cypari2
"""
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2*10**9)
pari.set_real_precision(38)

CURVES = {
    "11a1":   [0, -1, 1, -10, -20],
    "37a1":   [0, 0, 1, -1, 0],
    "389a1":  [0, 1, 1, -2, 0],
    "5077a1": [0, 0, 1, -7, 6],
    "571a1":  [0, -1, 1, -929, -10595],   # Sha of order 4
    "681b1":  [1, 1, 0, -1154, -15345],   # Sha of order 9
    "960d1":  [0, -1, 0, -900, -10098],   # Sha of order 4
    "234446a1": [1, -1, 0, -79, 289],     # rank 4
}

def check(label, ainv):
    E = pari.ellinit(ainv)
    E = pari.ellminimalmodel(E)
    r, Lr = pari.ellanalyticrank(E)
    r = int(r)
    Lr = Lr / pari.factorial(r)
    bsd = pari.ellbsd(E)                     # Omega * prod c_p / #tors^2
    if r == 0:
        reg = pari(1)
        gens = []
    else:
        rk = pari.ellrank(E)                 # [r_min, r_max, s, points]
        pts = rk[3]
        if int(rk[0]) != r or len(pts) != r:
            return f"{label}: 2-descent did not certify rank {r} (got {rk[0]}..{rk[1]})"
        gens = pari.ellsaturation(E, pts, 1000)
        reg = pari.matdet(pari.ellheightmatrix(E, gens))
    sha = Lr / (bsd * reg)
    return (f"{label:9s} r={r}  L*={float(Lr):.12f}  Omega*prod(c)/tors^2={float(bsd):.12f}"
            f"  Reg={float(reg):.12f}  Sha_an={float(sha):.10f}")


if __name__ == "__main__":
    for lab, a in CURVES.items():
        print(check(lab, a))
