import json,gzip,re,sys
src=sys.argv[1] if len(sys.argv)>1 else 'rank3.jsonl.gz'
rows=[]
for l in gzip.open(src,'rt'):
    x=json.loads(l)
    if x.get('vS',0)>=2:
        rows.append((x['p'],x['curve'],x['vS'],x['refine']['ar']))
rows.sort(key=lambda r:(r[0],int(re.match(r'\d+',r[1]).group()),r[1]))
def fmt(s,p,v):
    m=re.match(r'\s*(\d+)\*',s)
    d=int(m.group(1)) if m else 1
    pw='%d^{%d}'%(p,v)
    return '$'+pw+'$' if d==1 else '$%d\\cdot%s$'%(d,pw)
ent=[(c,str(p),fmt(a,p,v)) for p,c,v,a in rows]
G=3
out=['\\setlength{\\tabcolsep}{4pt}','\\begin{tabular}{'+'|'.join(['lrl']*G)+'}','\\hline',' & '.join(['curve & $p$ & $a_3$']*G)+'\\\\ \\hline']
for i in range(0,len(ent),G):
    ch=ent[i:i+G]; cells=[]
    for e in ch: cells+=list(e)
    while len(cells)<3*G: cells.append('')
    out.append(' & '.join(cells)+'\\\\')
out+=['\\hline','\\end{tabular}']
print('\n'.join(out))
