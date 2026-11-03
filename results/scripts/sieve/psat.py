"""p-saturation by the reduction sieve (Section 8 of the paper).
For a prime p and points P_1..P_r in E(Q): find good primes l (not dividing the
denominators, l != p) with p | #E(F_l) and cyclic p-Sylow; the map
v -> sum v_i P_i in E(F_l)/p E(F_l) = Z/p is phi_l(P) = dlog of (#E(F_l)/p) P.
If the vectors (phi_l(P_1),...,phi_l(P_r)) span F_p^r, the points are p-saturated.
Usage: psat.py "a1,a2,a3,a4,a6" "x1/z1:y1/z1;..." p1,p2,...  -> prints p ok|FAIL and the primes l used"""
import sys
import cypari2
pari = cypari2.Pari()
pari.allocatemem(2*10**9)

def rank_mod_p(rows, p):
    if not rows: return 0
    M = pari.matrix(len(rows), len(rows[0]), [x for r in rows for x in r])
    return int(pari.matrank(M * pari.Mod(1, p)))

def check(ai, pts, p, lmax=200000):
    E = pari.ellinit(ai)
    disc = int(E[11])
    den = 1
    for P in pts:
        den = int(pari.lcm(den, pari.denominator(P[0])))
    r = len(pts); rows = []; used = []
    l = 2
    while l < lmax:
        l = int(pari.nextprime(l + 1))
        if l == p or disc % l == 0 or den % l == 0:
            continue
        El = pari.ellinit(ai, l)
        Nl = int(pari.ellcard(El))
        if Nl % p:
            continue
        grp = pari.ellgroup(El, 0, 1)   # [order, structure, generators]
        cyc = [int(c) for c in grp[1]]
        if len(cyc) == 2 and cyc[1] % p == 0:
            continue                      # p-Sylow not cyclic: skip this l
        G = grp[2][0]
        m = Nl // p
        g = pari.ellmul(El, G, m)
        if g == [0]:
            continue
        row = []
        for P in pts:
            Pl = [pari.Mod(P[0], l), pari.Mod(P[1], l)]
            Q = pari.ellmul(El, Pl, m)
            if Q == [0]:
                row.append(0); continue
            k, acc = 1, g
            while acc != Q:
                acc = pari.elladd(El, acc, g); k += 1
                if k > p: raise RuntimeError('dlog failed')
            row.append(k)
        new = rows + [row]
        if rank_mod_p(new, p) > rank_mod_p(rows, p):
            rows = new; used.append(l)
        if len(rows) == r:
            return True, used
    return False, used

if __name__ == '__main__':
    ai = [int(x) for x in sys.argv[1].split(',')]
    pts = []
    for s in sys.argv[2].split(';'):
        x, y = s.split(':')
        pts.append([pari(x), pari(y)])
    for p in [int(x) for x in sys.argv[3].split(',')]:
        ok, used = check(ai, pts, p)
        print(p, 'ok' if ok else 'FAIL', used, flush=True)
