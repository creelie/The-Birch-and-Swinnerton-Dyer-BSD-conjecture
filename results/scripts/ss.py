"""Supersingular primes (Stein--Wuthrich Alg. 11.1, D_p-valued case): bound v(#Sha[p^oo]) by
ord_p of the omega-coordinates.  Usage: ss.py OUT.jsonl < pairs (allgens line|p)"""
import json, sys, time
from sage.all__sagemath_schemes import EllipticCurve, Qp, log
import sage.all__sagemath_eclib  # noqa
import sage.schemes.hyperelliptic_curves.monsky_washnitzer as _mw
from sage.rings.real_mpfr import RealField as _RF
def _log(x, b=None):  # the module only needs real logarithms of rationals; avoids sage.symbolic
    y = _RF(200)(x)
    return y.log(b) if b is not None else y.log()
_mw.log = _log
from certify import parse
with open(sys.argv[1], 'a') as out:
    for line in sys.stdin:
        g, p = line.rsplit('|', 1); p = int(p)
        lab, ai, r, pts = parse(g)
        E = EllipticCurve(ai); t = time.time()
        P = [E(x, y) for x, y in pts]
        E._EllipticCurve_rational_field__gens = {True: (P, True)} if False else None
        reg = E.padic_regulator(p, prec=12)
        rec_gens = [str(Q) for Q in E.gens()]
        K = reg[0].parent(); lg = K(1 + p).log()
        tam = E.tamagawa_product(); tors = E.torsion_order() ** 2
        bsdp = tam / tors / lg ** r * reg
        lp = E.padic_lseries(p, implementation='eclib')
        rec = dict(curve=lab, p=p, r=r, gens=rec_gens, bsd=[str(bsdp[0]), str(bsdp[1])],
                   vbsd=[int(bsdp[0].valuation()), int(bsdp[1].valuation())])
        for n in (3, 4):
            lps = lp.Dp_valued_series(n, prec=r + 1)
            lstar = [lps[0][r], lps[1][r]]
            low = [[str(lps[i][j]) for j in range(r)] for i in (0, 1)]
            rec[f'n{n}'] = dict(lstar=[str(x) for x in lstar], low=low)
            if lstar[0] != 0 and lstar[0].valuation() < lstar[0].precision_absolute():
                rec['v_lstar0'] = int(lstar[0].valuation()); rec['n'] = n
                break
        rec['sec'] = round(time.time() - t, 1)
        out.write(json.dumps(rec) + '\n'); out.flush()
