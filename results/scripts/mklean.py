"""Write a Lean file checking, for every certified pair (E, p) in the given JSONL files, the finite
arithmetic of the certificate (good ordinary reduction at p, the three Frobenius witnesses of
surjectivity) and that the generators lie on E.  Usage: mklean.py OUT.lean GENS.txt RES.jsonl..."""
import json, sys, collections
core = open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'lean', 'Core.lean')).read()
out, gensf, files = sys.argv[1], sys.argv[2], sys.argv[3:]
gens = {}
for line in open(gensf):
    t = line.split()
    if len(t) < 5: continue
    lab = t[0] + t[1] + t[2]
    gens[lab] = ([int(x) for x in t[3].strip('[]').split(',')], [tuple(int(u) for u in g.strip('[]').split(':')) for g in t[6:]])
cert = collections.defaultdict(dict)
extra = collections.defaultdict(set)
for f in files:
    for l in open(f):
        d = json.loads(l)
        if 'surj' in d and d.get('surj'):
            cert[d['curve']][d['p']] = tuple(d['surj'])
for f in files:
    for l in open(f):
        d = json.loads(l)
        if d.get('status') == 'certified':
            extra[d['curve']].add(d['p'])
def I(x): return f'({x})' if x < 0 else str(x)
with open(out, 'w') as o:
    o.write(core + '\nopen BSDCert\n\n')
    n = 0
    names = []
    for lab in sorted(extra, key=lambda s: (int(''.join(ch for ch in s if ch.isdigit() and True)[:-1] or 0), s)):
        ai, pts = gens[lab]
        A = ' '.join(I(a) for a in ai)
        lst = ', '.join(f'({p}, {cert[lab][p][0]}, {cert[lab][p][1]}, {cert[lab][p][2]})' for p in sorted(extra[lab]))
        P = ', '.join(f'({I(x)}, {I(y)}, {I(z)})' for x, y, z in pts)
        name = 'c' + lab
        o.write(f'-- {lab}: {len(extra[lab])} primes\n')
        ps = sorted(extra[lab]); chunks = [ps[i:i + 12] for i in range(0, len(ps), 12)]
        for k, ch in enumerate(chunks):
            lst = ', '.join(f'({p}, {cert[lab][p][0]}, {cert[lab][p][1]}, {cert[lab][p][2]})' for p in ch)
            o.write(f'set_option maxHeartbeats 0 in\ntheorem {name}_cert{k} : certAll {A} [{lst}] = true := by decide +kernel\n')
            names.append(f'{name}_cert{k}')
        o.write(f'theorem {name}_gens : allOn {A} [{P}] = true := by decide +kernel\n\n')
        names.append(f'{name}_gens')
        n += 1
    o.write('\n'.join(f'#print axioms {x}' for x in names) + '\n')
print(n, 'curves', sum(len(v) for v in extra.values()), 'pairs')
