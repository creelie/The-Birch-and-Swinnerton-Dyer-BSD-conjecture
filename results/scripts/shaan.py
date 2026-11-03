"""Analytic order of Sha, L^(r)(E,1)/(r! Omega c tors^-2 Reg), for the curves of rank3.txt, r4/r5/r6.  Usage: shaan.py OUT"""
import sys, json, cypari2
from math import factorial
pari = cypari2.Pari(); pari.allocatemem(2*10**9); pari.set_real_precision(38)
out = open(sys.argv[1], 'w')
for fn in ('rank3.txt', 'r5.txt', 'r6.txt'):
    for l in open(fn):
        f = l.split()
        if len(f) < 6: continue
        ai = pari(f[3]); pts = []
        for q in f[6:6+int(f[4])]:
            a, b, c = (pari(x) for x in q.strip('[]').split(':'))
            pts.append([a/c, b/c])
        E = pari.ellinit(ai); r, L = pari.ellanalyticrank(E)
        R = pari.matdet(pari.ellheightmatrix(E, pts)); c = pari.ellbsd(E)
        s = L / (factorial(int(r)) * c * R)
        out.write(json.dumps({'curve': f[0]+f[1]+f[2], 'r': int(r), 'sha_an': float(s)}) + '\n')
out.close()
