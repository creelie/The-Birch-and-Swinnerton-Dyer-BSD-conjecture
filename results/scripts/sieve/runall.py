import sys, json
sys.path.insert(0,'.')
from psat import check, pari
def pts_of(line):
    t=line.split(); r=int(t[4]); ai=[int(x) for x in t[3].strip('[]').split(',')]
    pts=[]
    for g in t[6:6+r]:
        x,y,z=[int(u) for u in g.strip('[]').split(':')]
        pts.append([pari(x)/z, pari(y)/z])
    return t[0]+t[1]+t[2], ai, pts
jobs=[]
P1000=[int(p) for p in pari.primes([5,997])]
jobs.append(('../r4src.txt', P1000))
out=open(sys.argv[1],'w')
for src,plist in [(l.split('|')[0], [int(x) for x in l.split('|')[1].split(',')]) for l in open(sys.argv[2]) if l.strip()]:
    lab, ai, pts = pts_of(src)
    for p in plist:
        ok, used = check(ai, pts, p)
        out.write(json.dumps(dict(curve=lab,p=p,ok=ok,ls=used))+'\n'); out.flush()
