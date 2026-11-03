"""Write paper/tab_leading.tex (pairs with v_p(S_p) >= 2 of the leading-coefficient check) and the count macro."""
import json, sys
d = [json.loads(l) for l in open(sys.argv[1])]
assert all(x['agree'] for x in d)
rows = sorted([x for x in d if x['v'] >= 2], key=lambda x: (int(''.join(c for c in x['curve'] if c.isdigit() and True) [:0] or 0), x['curve'], x['p']))
def key(x):
    lab = x['curve']; i = 0
    while lab[i].isdigit(): i += 1
    return (int(lab[:i]), lab[i:], x['p'])
rows = sorted(rows, key=key)
def digits(x):
    p, v = x['p'], x['v']; m = x['S'] // p**v
    ds = [m % p, (m // p) % p]
    terms = []
    for i, dgt in enumerate(ds):
        if dgt == 0: continue
        e = v + i
        terms.append((f'{dgt}\\cdot' if dgt != 1 else '') + f'{p}^{{{e}}}')
    return '+'.join(terms)
out = ['\\begin{tabular}{lrrl@{\\qquad}lrrl}', '\\hline', 'curve & $p$ & $v$ & $a_3\\equiv S_p$ & curve & $p$ & $v$ & $a_3\\equiv S_p$\\\\', '\\hline']
half = (len(rows) + 1) // 2
for i in range(half):
    cells = []
    for x in (rows[i], rows[i + half] if i + half < len(rows) else None):
        cells += [x['curve'], str(x['p']), str(x['v']), f'${digits(x)}$'] if x else ['', '', '', '']
    out.append(' & '.join(cells) + '\\\\')
out += ['\\hline', '\\end{tabular}']
open(sys.argv[2], 'w').write('\n'.join(out) + '\n')
print(len(d), len(rows))
