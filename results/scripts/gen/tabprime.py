import json,gzip
from collections import defaultdict
st=defaultdict(lambda:[0,0,0,0,0,0])
for l in gzip.open('rank3.jsonl.gz','rt'):
    x=json.loads(l)
    p=x['p']; v=x.get('vS',0)
    s=st[p]; s[0]+=1; s[1+v]+=1
    if (x['ap']-1)%p==0: s[5]+=1
rows=[]
tot=[0]*6
for p in sorted(st):
    s=st[p]; tot=[a+b for a,b in zip(tot,s)]
    rows.append('%d & %d & %d & %d & %d & %d & %d & %.2f\\\\'%(p,s[0],s[1],s[2],s[3],s[4],s[5],p*(s[0]-s[1])/s[0]))
rows.append('\\hline')
rows.append('all & %d & %d & %d & %d & %d & %d & \\\\'%tuple(tot))
out=['\\begin{tabular}{r|r|rrrr|r|r}','\\hline','$p$ & pairs & $v=0$ & $v=1$ & $v=2$ & $v=3$ & $a_p\\equiv1$ & $p\\cdot$irr.\\\\ \\hline']+rows+['\\hline','\\end{tabular}']
open('/home/user/The-Birch-and-Swinnerton-Dyer-BSD-conjecture/paper/tab_primes.tex','w').write('\n'.join(out)+'\n')
print('\n'.join(rows))
