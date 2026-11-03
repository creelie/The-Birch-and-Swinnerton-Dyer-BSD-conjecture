"""Merge the raw records into final per-pair statuses and print the summary."""
import json, glob, collections, gzip
def load(fs):
    out = []
    for f in fs:
        for l in open(f):
            out.append(json.loads(l))
    return out
# rank 3: base records then refinements (later files override)
base = {}
for d in load(['r3_final_raw.jsonl']):
    base[(d['curve'], d['p'])] = d
for d in load([f for f in ['r3_refine_0.jsonl','r3_refine_1.jsonl','r3_refine_2.jsonl','r3_refine4.jsonl','r3_refine5_0.jsonl','r3_refine5_1.jsonl','r3_refine6.jsonl','r3_refine7.jsonl','r3_refine8.jsonl']]):
    k = (d['curve'], d['p'])
    b = base[k]
    b['refine'] = {x: d[x] for x in ('n', 'vS', 'ar_val', 'ar_prec', 'ar', 'status') if x in d}
    if d['status'] == 'certified':
        b['status'] = 'certified'
        b['vS'] = d['vS']
    elif d['status'] == 'bound':
        b['status'] = 'bound'; b['sha_bound'] = d['sha_bound']
    else:
        b['status'] = 'undecided'; b['vS'] = d['vS']
st = collections.Counter(d['status'] for d in base.values())
curves = sorted(set(k[0] for k in base))
print('rank3 classes', len(curves), 'pairs', len(base), dict(st))
full = [c for c in curves if all(base[k]['status'] == 'certified' for k in base if k[0] == c)]
print('classes with every pair certified', len(full))
print('not certified:', sorted((k, base[k]['status'], base[k].get('vS')) for k in base if base[k]['status'] != 'certified'))
with gzip.open('rank3.jsonl.gz', 'wt') as o:
    for k in sorted(base, key=lambda k: (int(''.join(c for c in k[0] if c.isdigit())[:-1]), k)):
        o.write(json.dumps(base[k]) + '\n')
