"""Independent order-three enclosure, integrating signed arclength directly.

Only interval arithmetic is used to establish signs; no floating point
conversions, cached endpoint bounds or numerical search outputs are used.
"""
import json
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

here=Path(__file__).resolve().parent
from flint import arb, ctx
ctx.prec=144


def rational(r):
    r=Q(r)
    return arb(r.numerator)/r.denominator


def box(lo,hi):
    m=(lo+hi)/2
    return rational(m)+arb(0,rational(hi-m).upper())


def derivatives(z,b):
    x,y,ang,k,v=z
    si,co=ang.sin(),ang.cos()
    p=-x*co-y*si; q=-x*si+y*co
    A=-p-b*q-k**3/2
    B=k*q-b*(1+k*p)-3*k*k*v/2
    C=v*q+k*(1+k*p)-b*(v*p-k*k*q)-3*k*v*v-3*k*k*A/2
    return ([-si,co,k,v,A],[-k*co,-k*si,v,A,B],
            [-v*co+k*k*si,-v*si-k*k*co,A,B,C])


def step(z,b,h):
    ah=abs(h)
    first,second,_=derivatives(z,b)
    rad=[ah*(abs(a).upper()+1) for a in first]
    for _ in range(16):
        tube=[x+arb(0,r.upper()) for x,r in zip(z,rad)]
        tfirst,_,tthird=derivatives(tube,b)
        if all(ah*abs(a).upper()<r for a,r in zip(tfirst,rad)):
            return [x+h*f+h*h*g/2+h*h*h*j/6 for x,f,g,j in zip(z,first,second,tthird)]
        rad=[(3*r)/2+ah/8 for r in rad]
    raise ArithmeticError("Picard tube not certified")


def iv(parameters,n,den=64):
    d,k,v,b=parameters
    z=[d,arb(0),arb(0),k,v]
    h=arb(1 if n>=0 else -1)/den
    for _ in range(abs(n)):z=step(z,b,h)
    return z[:2]


def verify_cell(coords,p,n,depth=0):
    params=[box(a,b) for a,b in coords]
    x,y=iv(params,2*p); xx,yy=iv(params,-2*n)
    if x<-arb(1)/1024 and y>arb(1)/32 and xx<-arb(1)/1024 and yy<-arb(1)/32:
        return 1
    if depth==5:raise ArithmeticError(f"endpoint margins unverified {coords}")
    j=[3,2,1,0,3][depth]
    a,b=coords[j]; m=(a+b)/2
    return sum(verify_cell(coords[:j]+[(l,r)]+coords[j+1:],p,n,depth+1) for l,r in ((a,m),(m,b)))


def signed_triangle(coords,p,n):
    params=[box(a,b) for a,b in coords]
    d=params[0]
    x,y=iv(params,p); xx,yy=iv(params,n)
    sides=(d*y,x*yy-y*xx,-d*yy)
    eps=arb(1)/1024
    if all(a>eps for a in sides) or all(a<-eps for a in sides):
        return True
    return False


def main():
    data=json.loads((here/"certified.json").read_bytes())
    rows=data["certified_boxes"];assert len(rows)==320
    cells={tuple(tuple(p) for p in row[:4]) for row in rows}
    assert len(cells)==len(rows)
    required=set(product([(i,i+1) for i in range(1,5)],[(k,k+4) for k in range(16,32,4)],
                         [(v,v+8) for v in range(-16,16,8)],[(b,b+16) for b in range(-32,32,16)]))
    assert required.issubset(cells)
    checks=0
    for row in rows:
        coords=[(Q(a,16),Q(b,16)) for a,b in row[:4]]
        assert 0<row[4]<=44 and 0<row[5]<=44
        checks+=verify_cell(coords,row[4],row[5])
    # Negative curvature bends away from the origin at the initial section.
    # Dyadic input radii are reduced independently until all signs certify.
    outward=[]
    for d,k,v,b,p,n in [(Q(1,8),Q(-1,2),-2,0,-128,48),
            (Q(1,8),Q(-1,2),2,-2,128,-32)]:
        for den in (128,256,512,1024,2048,4096,8192):
            coords=[(Q(a)-Q(1,den),Q(a)+Q(1,den)) for a in (d,k,v,b)]
            if signed_triangle(coords,p,n):
                outward.append(dict(center=list(map(str,[d,k,v,b])),radius=f"1/{den}",
                                    signed_step_indices=[p,n],step_denominator=64,strict_det_margin="1/1024"))
                break
        else:
            raise ArithmeticError("negative curvature witness failed")
    report=dict(precision=ctx.prec,integrator_order=3,nominal_signed_step="±1/64",
                original_boxes_verified=len(rows),interval_subboxes=checks,
                fully_covered_product_boxes=len(required),outward_curvature_boxes=outward)
    (here/"replay.json").write_text(json.dumps(report,indent=2)+"\n")
    print(report)


if __name__=="__main__":main()
