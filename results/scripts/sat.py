"""p-saturation of the listed Mordell-Weil generators for all primes below B (eclib saturation).
Usage: sat.py B < curves (allgens lines)   -> prints label index"""
import sys
from sage.all__sagemath_schemes import EllipticCurve
import sage.all__sagemath_eclib  # noqa
from certify import parse
B = int(sys.argv[1])
for line in sys.stdin:
    if not line.strip(): continue
    lab, ai, r, pts = parse(line)
    E = EllipticCurve(ai)
    try:
        sat, index, reg = E.saturation([E(x, y) for x, y in pts], max_prime=B)
        print(lab, index, flush=True)
    except Exception as e:
        print(lab, 'ERR', repr(e)[:100], flush=True)
