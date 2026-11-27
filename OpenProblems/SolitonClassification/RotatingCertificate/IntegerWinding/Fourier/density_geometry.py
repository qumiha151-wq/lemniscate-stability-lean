"""Certified distinct critical radii and a lower bound for total angular variation."""
from bisect import bisect_left
from itertools import combinations
import json
from flint import arb, acb, ctx
from certificate import D


def check_density(path,shape):
    ctx.prec=140
    M=65536
    scale=10**8
    levels=4096
    data=json.loads(path.read_bytes())
    def coeff(key):
        return [acb(arb(a)/D,arb(b)/D) for a,b in data["rows"][key]]
    def samples(c):
        full=c+[acb(0)]*(M-2*len(c)+1)+[v.conjugate() for v in c[:0:-1]]
        return [z.real*M for z in acb.dft(full,inverse=True)]
    K,P,Q=[coeff(key) for key in ("k","p","q")]
    lam=arb(data["length_scale"])/D
    step=arb(61)/M
    err=arb(0,"1e-19")
    ps=[v+err for v in samples(P)]
    qs=[v+err for v in samples(Q)]
    radii=[(p*p+q*q).sqrt() for p,q in zip(ps,qs)]
    critical=shape["crossing_cells"]["q"]
    extrema=[]
    for j in critical:
        # q vanishes in the cell. The global component speed bound is 90.
        # The position has unit speed, so throughout r >= r_j-step.
        r=radii[j]
        extrema.append(r+arb(0,step*(abs(qs[j])+90*step)/(r-step)))
    ordering=sorted(range(len(critical)),key=lambda i:float(extrema[i]))
    assert all(extrema[a]<extrema[b] for a,b in zip(ordering,ordering[1:]))
    theta=samples([acb(0)]+[lam*c/acb(0,i) for i,c in enumerate(K[1:],1)])
    offset=theta[0]
    angles=[]
    two_pi=2*arb.pi()
    for j in range(M):
        tangent=theta[j]-offset+lam*K[0].real*(two_pi*j/M)+arb(0,"1e-16")
        arg=acb(qs[j],ps[j]).arg()
        x=(tangent+arg)/two_pi
        if j:
            shift=round(float(angles[-1]-x))
            x=x+shift
            assert abs(angles[-1]-x)<arb("0.01")
        angles.append(x)
    assert abs(angles[-1]-(angles[0]-1))<arb("0.01")
    def grid_angle(j):
        return angles[j%M]-(j//M)
    radius_twice=radii+radii
    rank={j:i for i,j in enumerate(ordering)}
    cuts=critical+[critical[0]+M]
    arms=[]
    for arm,(a,b) in enumerate(zip(cuts,cuts[1:])):
        nxt=(arm+1)%len(critical)
        increasing=rank[arm]<rank[nxt]
        ids=list(range(a+1,b+1))
        if not increasing:
            ids.reverse()
        approx=[float(radius_twice[j]) for j in ids]
        vals={}
        for m in range(max(1,int(approx[0]*levels)),int(approx[-1]*levels)+2):
            v=arb(m)/levels
            ix=bisect_left(approx,m/levels)
            if not 0<ix<len(approx):
                continue
            left,right=ids[ix-1],ids[ix]
            if not (radius_twice[left]<v and radius_twice[right]>v):
                continue
            assert abs(left-right)==1
            j=min(left,right)
            min_r=radius_twice[j]-step
            ang=grid_angle(j)+arb(0,step/(two_pi*min_r))
            # Use verified outward integer endpoints to sum many variations exactly.
            coarse=ang*scale
            lo=int(float(coarse.lower()))-2
            hi=int(float(coarse.upper()))+2
            assert coarse>lo and coarse<hi
            vals[m]=(lo,hi)
        arms.append(vals)

    total=0
    for a,b in combinations(arms,2):
        optimum=None
        for m in sorted(a.keys() & b.keys()):
            left=a[m][0]-b[m][1]
            right=a[m][1]-b[m][0]
            if optimum is None:
                optimum=(left,right)
                continue
            l,r=optimum
            if left>r:
                total+=left-r
                optimum=(left,left)
            elif right<l:
                total+=l-right
                optimum=(right,right)
            else:
                optimum=(max(l,left),min(r,right))
    assert total > 1009*scale//100
    return dict(radial_arms=len(arms),distinct_critical_radii=len(extrema),
                variation_lower_numerator=total,variation_lower_denominator=scale)
