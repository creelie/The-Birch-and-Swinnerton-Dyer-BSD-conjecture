"""Filter the raw arXiv harvest of arxiv_cat.py into the catalogue files.

Usage: python3 build_catalogue.py raw.json out_dir
Keeps a record if its title or abstract names an object of the conjecture,
drops fluid-dynamics "Euler system" hits, and flags math.GM records.
"""
import csv, json, re, sys

STRONG = re.compile(r'birch|swinnerton|selmer|shafarevich|heegner|kolyvagin|gross[- ]zagier|'
                    r'iwasawa|elliptic curve|abelian variet|congruent number|bloch[- ]kato|tamagawa|'
                    r'p-adic l-function|mordell[- ]weil|modular form|motiv', re.I)
EULER = re.compile(r'euler system', re.I)
CTX = re.compile(r'galois|l-function|kato|cohomolog|arithmetic', re.I)
DROP_PRIMARY = {'math.AP', 'math.NA'}
DROP_IDS = {'2501.06792', '2407.17340', '1711.01202', '2004.11950', '2101.10910', '2101.11114'}
COLS = ['id', 'published', 'updated', 'primary', 'authors', 'title', 'doi', 'journal_ref', 'topics', 'flag']


def clean(s):
    return re.sub(r'\s+', ' ', s or '').strip()


def main(raw, out):
    keep = []
    for r in json.load(open(raw)):
        text = r['title'] + ' ' + r['abstract']
        if r['primary'] in DROP_PRIMARY or r['id'].split('v')[0] in DROP_IDS:
            continue
        if not (STRONG.search(text) or (EULER.search(text) and CTX.search(r['abstract']))):
            continue
        keep.append(dict(id=r['id'], published=r['published'][:10], updated=r['updated'][:10],
                         primary=r['primary'], authors='; '.join(r['authors']), title=clean(r['title']),
                         doi=r.get('doi') or '', journal_ref=clean(r.get('journal_ref')),
                         topics=';'.join(r.get('tags', [])),
                         flag='math.GM: unrefereed general mathematics' if r['primary'] in ('math.GM', 'physics.gen-ph') else '',
                         abstract=clean(r['abstract'])))
    keep.sort(key=lambda x: x['published'], reverse=True)
    json.dump(keep, open(f'{out}/arxiv_bsd_catalogue.json', 'w'), indent=1, ensure_ascii=False)
    with open(f'{out}/arxiv_bsd_catalogue.tsv', 'w', newline='') as f:
        w = csv.writer(f, delimiter='\t', lineterminator='\n')
        w.writerow(COLS)
        for k in keep:
            w.writerow([k[c] for c in COLS])
    print(len(keep), 'records')


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
