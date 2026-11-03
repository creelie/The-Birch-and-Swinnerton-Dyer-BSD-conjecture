"""Worked example of the p-adic sigma function for E4 at p = 5 (PARI)."""
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
src = open(__file__.replace('.py', '.gp')).read()
for line in src.strip().splitlines():
    r = pari(line.rstrip(';'))
