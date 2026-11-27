"""Interval evaluation of the whole Fourier curve and transversal zero counts.
The analytic transfer from the validated shooting orbit is in WholeOrbitFourier.md.
"""
from certificate import here,D,names,verify,json,sys,Fraction
from flint import arb,acb,ctx
from hashlib import sha256
from pathlib import Path
import argparse

def checks(path,center_path):
    ctx.prec=140
    packet=json.loads(path.read_bytes())
    r=verify(path)
    den=int(r["residual_denominator"])
    assert all(2*10**35*int(x)<den for x in r["l1_residual_numerators"])
    assert 9*D < packet["length_scale"] < 10*D
    seed=json.loads(center_path.read_bytes())
    center=list(map(Fraction,seed["center"]))
    e,g=map(Fraction,seed["phase"])
    ds=lambda n: Fraction(2*sum(a for a,b in packet["rows"][n])-packet["rows"][n][0][0], D)
    errors=[ds(n)-v for n,v in zip(names,[center[0],e*center[3]/8,center[1],g*center[3]])]
    assert max(map(abs,errors))<Fraction(1,10**38)
    assert abs(Fraction(packet["pitch"],D)-center[4])<Fraction(1,10**38)
    assert abs(arb(packet["length_scale"])/D*arb.pi()-arb(seed["center"][2]))<arb("1e-38")
    M=65536
    pitch=arb(packet["pitch"])/D+arb(0,"1e-28")
    grid=[]
    for key in names:
        c=[acb(arb(a)/D,arb(b)/D) for a,b in packet["rows"][key]]
        f=c+[acb(0)]*(M-2*len(c)+1)+[v.conjugate() for v in c[:0:-1]]
        grid.append([z.real*M+arb(0,"1e-19") for z in acb.dft(f,inverse=True)])
    dsmax=arb(61)/M
    e0=arb(0,1)
    counts={key:[] for key in names}
    margin=arb(10)
    for j in range(M):
        start=[v[j] for v in grid]
        state=[s+90*dsmax*e0 for s in start]
        def rhs(box):
            k,v,p,q=box
            return [8*v,-k*k*k/16-(p+pitch*q)/8,-k*q,1+k*p]
        for _ in range(3):
            state=[s+abs(v)*dsmax*e0 for s,v in zip(start,rhs(state))]
        field=rhs(state)
        for i,n in enumerate(names):
            a,b=start[i],grid[i][(j+1)%M]
            assert not a.contains(0) and not b.contains(0),(j,n,"node")
            if state[i].contains(0):
                assert not field[i].contains(0),(j,n,"ambiguous",state[i],field[i])
                if (a>0)!=(b>0):
                    counts[n].append(j)
                    margin=margin.min(abs(field[i]))
            else:
                assert (a>0)==(b>0)
    return dict(packet_sha256=sha256((json.dumps(packet,separators=(",",":"))+"\n").encode()).hexdigest(),
        center_sha256=sha256(center_path.read_bytes()).hexdigest(),
        grid_size=M,transfer_radius="1e-19",residual_bound="5e-36",crossing_cells=counts,
        counts={k:len(v) for k,v in counts.items()},minimum_absolute_arclength_derivative=str(margin))

