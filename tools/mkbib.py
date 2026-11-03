"""Build references.bib from (key, DOI, clean title, topic) via Crossref metadata."""
import json, sys, time, urllib.request, re
rows=[l.rstrip('\n').split('|') for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
out=[]; rep=[]
def tex(s): return s.replace('&amp;','\\&').replace('&','\\&')
for key,doi,title,topic in rows:
    import os
    cache=os.environ.get('CROSSREF_CACHE','.crossref_cache'); cf=os.path.join(cache,doi.replace('/','_')+'.json')
    os.makedirs(cache,exist_ok=True)
    if os.path.exists(cf): m=json.load(open(cf))
    else:
        for att in range(8):
            try:
                m=json.load(urllib.request.urlopen(urllib.request.Request(f'https://api.crossref.org/works/{doi}?mailto=bsd-lit@example.org'),timeout=60))['message']; break
            except Exception as e:
                time.sleep(5*(att+1))
        json.dump(m,open(cf,'w'))
    au=' and '.join(f"{a.get('family','')}, {a.get('given','')}".strip(', ') for a in m.get('author',[]) if 'family' in a)
    ed=' and '.join(f"{a.get('family','')}, {a.get('given','')}".strip(', ') for a in m.get('editor',[]) if 'family' in a)
    yr=(m.get('published-print') or m.get('issued'))['date-parts'][0][0]
    typ=m.get('type')
    cont=' '.join(m.get('container-title',[]))
    f={'title':'{'+title+'}','doi':doi.lower(),'year':str(yr)}
    if au: f['author']=au
    if typ=='journal-article':
        et='article'; f['journal']=tex(cont)
        if m.get('volume'): f['volume']=m['volume']
        if m.get('issue'): f['number']=m['issue']
        if m.get('page'): f['pages']=m['page'].replace('-','--')
    elif typ in ('book-chapter','proceedings-article'):
        et='incollection'; f['booktitle']=tex(cont) or tex(' '.join(m.get('container-title',[])))
        if m.get('page'): f['pages']=m['page'].replace('-','--')
        if m.get('publisher'): f['publisher']=tex(m['publisher'])
        if ed: f['editor']=ed
    else:
        et='book'; f['publisher']=tex(m.get('publisher',''))
        if cont: f['series']=tex(cont)
        if not au and ed: f['editor']=ed
    f['keywords']=topic
    body=',\n'.join(f'  {k} = {{{v}}}' if not v.startswith('{') else f'  {k} = {v}' for k,v in f.items())
    out.append(f'@{et}{{{key},\n{body}\n}}\n')
    rep.append(f"{key}\t{doi}\t{yr}\t{au[:60]}\t{cont[:50]}\t{typ}")
    time.sleep(1.2)
open(sys.argv[2],'w').write('\n'.join(out))
print('\n'.join(rep))
