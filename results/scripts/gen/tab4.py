import json, sys
d=[json.loads(l) for l in open(sys.argv[1] if len(sys.argv) > 1 else '../../data/rank4.jsonl')]
d=[x for x in d if 'p' in x]
d.sort(key=lambda x:x['p'])
ent=[]
for x in d:
    p=x['p']
    if p==7: a='$3\\cdot7$'
    elif p==157: a='$34\\cdot157$'
    else: a=str(x['ar'])
    w='%d,%d,%d'%tuple(x['surj'])
    ent.append((str(p),a,w))
G=4
rows=[]
for i in range(0,len(ent),G):
    chunk=ent[i:i+G]
    cells=[]
    for e in chunk: cells+=list(e)
    while len(cells)<3*G: cells.append('')
    rows.append(' & '.join(cells)+'\\\\')
out=['\\setlength{\\tabcolsep}{3pt}','\\begin{tabular}{'+'|'.join(['rrl']*G)+'}','\\hline',
 ' & '.join(['$p$ & $a_4$ & witness']*G)+'\\\\ \\hline']+rows+['\\hline','\\end{tabular}']
open('/home/user/The-Birch-and-Swinnerton-Dyer-BSD-conjecture/paper/tab_rank4.tex','w').write('\n'.join(out)+'\n')
print(len(ent),len(rows))
