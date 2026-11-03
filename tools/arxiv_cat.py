import urllib.request, urllib.parse, time, xml.etree.ElementTree as ET, json, sys
NS={'a':'http://www.w3.org/2005/Atom','x':'http://arxiv.org/schemas/atom'}
queries={
 'bsd':'all:"Swinnerton-Dyer"',
 'bsd2':'abs:"BSD conjecture"',
 'sha':'all:"Tate-Shafarevich"',
 'sha2':'all:"Shafarevich-Tate"',
 'heegner':'all:"Heegner points" OR all:"Heegner point"',
 'kolyvagin':'all:Kolyvagin',
 'gz':'all:"Gross-Zagier"',
 'imc':'all:"main conjecture" AND all:"elliptic curve"',
 'selmer':'all:Selmer AND all:"elliptic curve"',
 'padicL':'all:"p-adic L-function" AND all:"elliptic curve"',
 'rankavg':'all:"average rank" AND all:"elliptic curve"',
 'congruent':'all:"congruent number"',
 'goldfeld':'all:Goldfeld AND all:twists AND all:rank',
 'parity':'all:"parity conjecture"',
 'eulersys':'all:"Euler system" AND all:"elliptic"',
 'rankrecord':'all:"elliptic curve" AND all:"large rank"',
 'bloch_kato':'all:"Bloch-Kato conjecture"',
}
out={}
for tag,q in queries.items():
    start=0
    while True:
        url='https://export.arxiv.org/api/query?'+urllib.parse.urlencode({'search_query':q,'start':start,'max_results':200,'sortBy':'submittedDate','sortOrder':'ascending'})
        for att in range(5):
            try:
                data=urllib.request.urlopen(url,timeout=120).read(); break
            except Exception as e:
                time.sleep(10)
        root=ET.fromstring(data)
        tot=int(root.find('{http://a9.com/-/spec/opensearch/1.1/}totalResults').text)
        ents=root.findall('a:entry',NS)
        for e in ents:
            aid=e.find('a:id',NS).text.split('/abs/')[-1]
            base=aid.rsplit('v',1)[0] if 'v' in aid.split('/')[-1] else aid
            rec=out.setdefault(base,{'id':base,'title':' '.join(e.find('a:title',NS).text.split()),
              'authors':[a.find('a:name',NS).text for a in e.findall('a:author',NS)],
              'published':e.find('a:published',NS).text[:10],
              'updated':e.find('a:updated',NS).text[:10],
              'primary':e.find('x:primary_category',NS).attrib['term'],
              'doi':(e.find('x:doi',NS).text if e.find('x:doi',NS) is not None else ''),
              'journal_ref':(' '.join(e.find('x:journal_ref',NS).text.split()) if e.find('x:journal_ref',NS) is not None else ''),
              'abstract':' '.join(e.find('a:summary',NS).text.split()),'tags':[]})
            if tag not in rec['tags']: rec['tags'].append(tag)
        print(tag,start,len(ents),tot,file=sys.stderr,flush=True)
        start+=200
        time.sleep(3.5)
        if start>=tot or not ents: break
json.dump(sorted(out.values(),key=lambda r:r['published']),open(sys.argv[1],'w'),indent=0,ensure_ascii=False)
print(len(out))
