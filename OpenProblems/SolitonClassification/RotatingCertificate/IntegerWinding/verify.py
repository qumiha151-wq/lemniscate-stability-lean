"""Close the nonlinear shadowing, contraction, polar-index and period bounds."""
from math import isqrt
import json
from pathlib import Path
from trajectory import here, source, digest, matrix_norm, vmax, arb, ctx
from flint import arb_mat

def check():
    ctx.dps=85
    reports=[json.loads((here/name).read_bytes()) for name in ["plus.json","minus.json"]]
    seed=json.loads((here/"center.json").read_bytes())
    c=list(map(arb,seed["center"]))
    phase=list(map(arb,seed["phase"]))
    K=arb(20000); I=arb(20000); L=arb(18); A=arb(90); Hess=arb(4); T=arb(32)
    r=arb("1e-30");R=arb("1e-42");Ru=2*r
    h=c[2]/4000
    assert h<arb(".008") and c[2]+r<31 and c[2]-r>30 and c[4]-r>arb(".1")
    assert 3*arb(9)**2/16+(1+arb(".2")+9)/8<L
    assert 3*arb(9)/8+arb(1)/4<Hess
    assert L <= 3*A/10 and Hess/2<=3*A/100 and arb(1)/16<=A/1000
    assert 15000*(L*h).exp()<K and 15000*(L*h).exp()<I
    for outer,inner,speed in zip(["9","5","9","9"],["8.4","4.35","7.25","7.25"],[40,47,81,82]):
        assert arb(outer)-arb(inner)-h*speed>arb(".05")
    assert 8*arb(5)<=40 and arb(9)**3/16+arb(9)/8+arb(".2")*9/8<47 and 82<A
    C=I*Hess*K*K/2
    E=K*R
    upper=arb(0)
    for rep,sign in zip(reports,[1,-1]):
        assert (rep["sign"],rep["n"],rep["order"],rep["dps"])==(sign,4000,60,85)
        assert rep["center"]==digest(here/"center.json") and rep["own"]==digest(here/"trajectory.py")
        assert rep["kernel"]==digest(source)
        assert arb(rep["maxK"])<15000 and arb(rep["maxI"])<15000
        assert all(arb(x)<arb(y) for x,y in zip(rep["maxState"],["8.4","4.35","7.25","7.25",".15"]))
        sigma=arb(rep["initialRound"])+I*arb(rep["xjump"])
        jump=I*arb(rep["mjump"])
        assert (sigma+T*C*R**2)*jump.exp()<R
        assert (r+sigma+T*C*Ru**2)*jump.exp()<Ru
        assert jump<arb(".25") and (T*I*Hess*K*K*Ru+2*jump).exp()<2
        assert (L*r).exp()<2 and K*Ru+A*r<arb("1e-18") and K*Ru+A*r<arb(".05")
        upper=upper.max(K*(T*I*Hess*K*K*R+jump).expm1())
        assert arb(rep["radius"])>arb(".16")
    hess=16*(T*(4*K)*(4*I)*Hess*(4*K)**2+2*L*(4*K)+L*A)
    err=16*upper+16*L*E
    init=arb_mat(6,5)
    init[0,0]=1;init[2,1]=1;init[1,3]=phase[0]/8;init[3,3]=phase[1];init[4,4]=1
    assert matrix_norm(init)<=1
    ep=[[arb(x) for x in rep["endpoint"]] for rep in reports]
    Y=[arb_mat([[arb(x) for x in row] for row in rep["matrix"]]) for rep in reports]
    def field(x):
        k,u,p,q,b,_=x
        return [8*u,-k**3/16-p/8-b*q/8,-k*q,1+k*p,arb(0),k]
    fp,fm=map(field,ep)
    J6=(Y[0]-Y[1])*init
    for i in range(6):J6[i,2]=fp[i]+fm[i]
    rows=[0,1,2,3,5]; weights=[1,8,1,1,1]
    J=arb_mat([[weight*J6[row,j]+arb(0,err) for j in range(5)] for row,weight in zip(rows,weights)])
    rawF=[weight*(ep[0][row]-ep[1][row]) for row,weight in zip(rows,weights)]
    rawF[-1]+=2*arb.pi()
    F=arb_mat([[x+arb(0,16*E)] for x in rawF])
    approx=J.inv()
    B=arb_mat([[approx[i,j].mid() for j in range(5)] for i in range(5)])
    assert abs(B.det())>0
    eye=arb_mat([[int(i==j) for j in range(5)] for i in range(5)])
    bn=matrix_norm(B)
    lip=matrix_norm(eye-B*J)+bn*hess*r
    eta=matrix_norm(B*F)
    assert lip<arb(".01") and eta+lip*r<r,(lip,eta,r)
    k,p,half,alpha,b=c
    z0=[k,alpha*phase[0]/8,p,alpha*phase[1],b,arb(0)]
    assert 8*field(z0)[1]+arb(0,8*L*r)<-200
    angle=arb(reports[0]["angle"])-arb(reports[1]["angle"])
    assert abs(angle)<arb(".001")
    assert 9+1/(arb(".16")-arb(".008")) < 16
    assert arb(".008")*16<arb.pi()/2
    assert 2*(half+r)*L/4<300
    primeChecks=reports[0]["primeChecks"]
    primes=[p for p in range(2,301) if all(p%j for j in range(2,isqrt(p)+1))]
    assert set(primeChecks)=={str(p) for p in primes}
    for d in primes:
        x=primeChecks[str(d)]
        assert x["node"]==(16000+d)//(2*d) and arb(x["gap"])>arb(".001")
    out=dict(status="Passed interval checks; analytic proof in IntegerRotatingWinding.md; not verified in Lean",
             r=r.str(55),eta=eta.str(55),lip=lip.str(55),inverseNorm=bn.str(55),hessian=hess.str(55),
             true_center_residual=[F[i,0].str(55) for i in range(5)],support_angle=angle.str(55),
             support_index=0,centre_winding=-1,turning=-1,minimum_radius_lower=".152",primitive_support=True,
             files={p:digest(here/p) for p in ["center.json","plus.json","minus.json","trajectory.py","verify.py"]},
             kernel_sha256=digest(source))
    (here/"certificate.json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))

if __name__=="__main__":
    check()
