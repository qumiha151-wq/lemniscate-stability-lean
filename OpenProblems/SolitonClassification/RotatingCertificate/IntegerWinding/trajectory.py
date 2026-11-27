"""Validated grid, support-angle increments and shorter-period tests for one half orbit."""
import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
source = here.parent/"classification_odd_branch_interval"/"validated_metric_shoot.py"
sys.path.insert(0,str(here.parents[1]/"pydeps"))
sys.path.insert(0,str(source.parent))
from validated_metric_shoot import step, full_matrix, matrix_norm, vmax, ROWS
from flint import arb,ctx

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def evaluate(sign):
    ctx.dps=85
    N,order=4000,60
    seed = json.loads((here/"center.json").read_bytes())
    k,p,half,alpha,b=map(arb,seed["center"])
    e,g=map(arb,seed["phase"])
    raw=[k,alpha*e/8,p,alpha*g,b,arb(0)]
    state=[x.mid() for x in raw]
    init=state[:]
    sens=[[arb(int(ROWS[i]==j)) for j in range(5)] for i in range(5)]
    stepSize=sign*half/N
    ratio=18*abs(stepSize)
    tail=10*ratio**(order+1)/(1-ratio)
    variationTail=ratio**(order+1)*((2*order+3)/(1-ratio)+2*ratio/(1-ratio)**2)
    xjump=arb(0);mjump=arb(0)
    maxK=arb(0);maxI=arb(0)
    maxState=[arb(0) for _ in state]
    radius=arb(100)
    angle=arb(0)
    previous=None
    inflation=arb("1e-18")
    denominators={}
    for d in range(2,301):
        if all(d%i for i in range(2,isqrt(d)+1)):
            j=(4*N+d)//(2*d)
            denominators.setdefault(j,[]).append(d)
    primeChecks={}
    for j in range(N+1):
        for i in range(6):
            maxState[i]=maxState[i].max(abs(state[i]))
        for z,cap in zip(state,["8.4","4.35","7.25","7.25",".15"]):
            assert abs(z)<arb(cap),(sign,j,z,cap)
        Y=full_matrix(sens)
        K,I=matrix_norm(Y),matrix_norm(Y.inv())
        assert K<15000 and I<15000,(sign,j,K,I)
        maxK=maxK.max(K);maxI=maxI.max(I)
        # The analytic proof gives an error < 1e-18 at each fractional true-root time.
        p,q=[state[i]+arb(0,inflation) for i in (2,3)]
        radius=radius.min((p*p+q*q).sqrt())
        if previous is not None:
            pp,qq=previous
            dot=q*qq+p*pp
            assert dot>0
            angle+=((qq*p-pp*q)/dot).atan()
        previous=p,q
        if sign==1:
            for d in denominators.get(j,[]):
                dt=abs(2*half/d-j*stepSize)+arb("3e-30")
                gaps=[abs(state[i]-init[i])-2*inflation-dt*M for i,M in enumerate([40,47,81,82])]
                gap=vmax(gaps)
                assert gap>arb(".001"),(d,j,gap)
                primeChecks[str(d)]=dict(node=j,gap=gap.str(60))
        if j==N:break
        state,sens,xround,mround=step(state,sens,stepSize,order)
        xjump+=xround+tail
        mjump+=mround+K*variationTail
        if (j+1)%500==0:print(sign,j+1,flush=True)
    assert radius>arb(".16")
    out=dict(sign=sign,n=N,order=order,dps=85,center=digest(here/"center.json"),
             kernel=digest(source),own=digest(Path(__file__)),
             initialRound=vmax([x.rad() for x in raw]).str(75),xjump=xjump.str(75),mjump=mjump.str(75),
             maxK=maxK.str(75),maxI=maxI.str(75),maxState=[x.str(75) for x in maxState],
             radius=radius.str(75),angle=angle.str(75),primeChecks=primeChecks,
             endpoint=[x.str(75) for x in state],
             matrix=[[Y[i,j].str(75) for j in range(6)] for i in range(6)])
    (here/("plus.json" if sign==1 else "minus.json")).write_text(json.dumps(out,indent=2)+"\n")

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("sign",type=int,choices=[-1,1])
    evaluate(parser.parse_args().sign)
