import json,gzip,re,cypari2
pari=cypari2.Pari(); pari.allocatemem(10**9)
cur={}
for l in open('rank3.txt'):
    t=l.split(); lab=t[0]+t[1]+t[2]
    ai=[int(x) for x in t[3].strip('[]').split(',')]
    pts=[]
    for g in t[6:9]:
        x,y,z=[int(u) for u in g.strip('[]').split(':')]
        pts.append([pari(x)/z,pari(y)/z])
    cur[lab]=(ai,pts)
agree=dis=0;bad=[]
for l in gzip.open('rank3.jsonl.gz','rt'):
    x=json.loads(l)
    if x.get('vS',0)==0: continue
    p=x['p'];v=x['vS']; ai,pts=cur[x['curve']]
    E=pari.ellinit(ai)
    R=pari.ellpadicregulator(E,p,v+8,pts)
    lg=pari(f'log(1+{p}+O({p}^{v+10}))')
    al=[a for a in pari(f'polrootspadic(x^2-({x["ap"]})*x+{p},{p},{v+10})') if pari.valuation(a,p)==0][0]
    gr=pari.ellglobalred(E); tam=gr[2]; tors=pari.elltors(E)[0]
    S=(1-1/al)**2*tam*R/lg**3/tors**2
    assert int(pari.valuation(S,p))==v
    dS=int(pari.truncate(S/pari(p)**v))%p
    m=re.match(r'\s*(\d+)\*',x['refine']['ar']) if 'refine' in x else None
    s=x['refine']['ar'] if 'refine' in x else None
    if m: da=int(m.group(1))
    else:
        mm=re.match(r'\s*(\d+)\^',s) or re.match(r'\s*(\d+) ',s)
        da=1
    if da==dS: agree+=1
    else: dis+=1; bad.append((x['curve'],p,v,s,dS))
print(agree,dis); print(bad[:20])
