import cypari2
pari=cypari2.Pari(); pari.allocatemem(2*10**9)
def run(ai,pts,p,prec=8):
    E=pari.ellinit(ai); E=pari.ellminimalmodel(E)
    print('cond',pari.ellglobalred(E)[0],'tam',pari.ellglobalred(E)[2],'tors',pari.elltors(E)[0])
    ap=pari.ellap(E,p); print('ap',ap,'#E(F_p)',p+1-ap)
    P=pari(pts)
    R=pari.ellpadicregulator(E,p,prec,P)
    print('Reg_p',R)
    L=pari('log(1+%d+O(%d^%d))'%(p,p,prec+1)); print('log(1+p)',L)
    r=len(pts); Rg=R/L**r; print('Reg_gamma',Rg)
    # unit root
    x=pari('x'); 
    al=pari.polrootspadic(x**2-ap*x+p,p,prec+2); print('roots',al)
    a=[z for z in al if pari.valuation(z,p)==0][0]
    f=(1-1/a)**2; print('(1-1/alpha)^2',f)
    c=pari.ellglobalred(E)[2]; t=pari.elltors(E)[0]
    S=f*c*Rg/t**2; print('S_p',S)
    M=pari.ellpadicheightmatrix(E,p,prec,P); s2=pari.ellpadics2(E,p,prec)
    H=M[0]-s2*M[1]  # check conventions
    print('H',H)
run([1,1,0,-39,-59],[[-3,8],[10,21],[-5,9]],5)
run([0,1,1,-65,195],[[-5,20],[pari('21/4'),pari('37/8')],[pari('37/9'),pari('89/27')]],89,7)
run([1,-1,0,-79,289],[[6,-1],[4,3],[5,-2],[8,7]],7)
