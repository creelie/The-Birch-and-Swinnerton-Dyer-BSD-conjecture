import urllib.request, urllib.parse, json, sys, time
items=[l.rstrip('\n').split('|',1) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
out={}
for key,q in items:
    url='https://api.crossref.org/works?'+urllib.parse.urlencode({'query.bibliographic':q,'rows':3,'mailto':'bsd-lit@example.org'})
    for a in range(4):
        try: d=json.load(urllib.request.urlopen(url,timeout=60)); break
        except Exception as e: time.sleep(5); d=None
    hits=[]
    for it in (d or {}).get('message',{}).get('items',[]):
        au=', '.join((x.get('family','')) for x in it.get('author',[])[:6])
        yr=(it.get('issued',{}).get('date-parts',[[None]])[0][0])
        hits.append({'doi':it.get('DOI'),'title':' '.join(it.get('title',[''])),'authors':au,'year':yr,
          'container':' '.join(it.get('container-title',[''])),'volume':it.get('volume',''),'page':it.get('page',''),'type':it.get('type')})
    out[key]=hits
    h=hits[0] if hits else {}
    print(f"{key} :: {h.get('doi')} :: {h.get('authors')} ({h.get('year')}) {h.get('title')[:90] if h else ''} :: {h.get('container')} {h.get('volume')} {h.get('page')}",flush=True)
    time.sleep(0.5)
json.dump(out,open(sys.argv[2],'w'),indent=1)
