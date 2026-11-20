"""Rigorous interval propagation through rotating bases, including uncertain shooting data."""
import json
from math import factorial
from pathlib import Path
here=Path(__file__).resolve().parent
from flint import arb,arb_mat,ctx
from edge3_hull import jets,field,cross

scale=[8,64,8,8,1,1]
eye=arb_mat([[int(i==j) for j in range(6)] for i in range(6)])
zero=arb(0)


def tube_for(z,b,h):
    ah=abs(h)
    widths=[2*ah*abs(f).upper()+arb(1)/128 for f in field(z,b)]
    for _ in range(16):
        tube=[u+arb(0,r.upper()) for u,r in zip(z,widths)]
        needed=[ah*abs(f).upper() for f in field(tube,b)]
        if all(a<b for a,b in zip(needed,widths)):return tube
        widths=[max(r,2*n+ah/128) for r,n in zip(widths,needed)]
    raise ArithmeticError("local IVP tube")


def transform_jacobian(tube,b,h,terms=6):
    k,v,p,q,t=tube
    J=[[0,1,0,0,0,0],[-3*k*k/2,0,-1,-b,0,-q],[-q,0,0,-k,0,0],
       [p,0,k,0,0,0],[1,0,0,0,0,0],[0,0,0,0,0,0]]
    A=arb_mat([[arb(J[i][j])*scale[j]*h/scale[i] for j in range(6)] for i in range(6)])
    r=max(sum(abs(A[i,j]).upper() for j in range(6)) for i in range(6))
    if not r<1: raise ArithmeticError("local Jacobian too large")
    tail=(r**(terms+1)/factorial(terms+1)/(1-r/(terms+2))).upper()
    P=eye;Y=eye
    for m in range(1,terms+1):
        P=A*P/m;Y=Y+P
    return Y+arb_mat([[arb(0,tail) for _ in range(6)] for _ in range(6)])


def basis(M):
    cols=[]
    for j in range(6):
        v=[M[i,j].mid() for i in range(6)]
        for u in cols:
            a=sum(x*y for x,y in zip(u,v))
            v=[c-a*q for c,q in zip(v,u)]
        n=sum(x*x for x in v).sqrt()
        cols.append([(c/n).mid() for c in v])
    return arb_mat([[cols[j][i] for j in range(6)] for i in range(6)])


def evolve(center,times,radius,den=256):
    ctx.prec=176
    sign=1 if max(times)>0 else -1
    h=arb(sign)/den
    k,v,p,q,b=[arb(s)+arb(0,radius) for s in center]
    ini=[k,v,p,q,zero,b]; c=[a.mid() for a in ini]
    err=arb_mat([[arb(0,(abs(a-d)/s).upper())] for a,d,s in zip(ini,c,scale)])
    Q=eye;found={}
    stride=den//128
    assert den==128*stride
    for i in range(stride*max(map(abs,times))+1):
        eq=Q*err
        zz=[u+eq[j,0]*scale[j] for j,u in enumerate(c)]
        if i%stride==0 and sign*i//stride in times:
            k,v,p,q,t,b=zz
            found[sign*i//stride]=(q*t.cos()-p*t.sin(),q*t.sin()+p*t.cos())
        if i==stride*max(map(abs,times)):break
        if any(abs(eq[j,0])*scale[j]>arb(3)/100 for j in range(6)):raise ArithmeticError("interval too broad")
        tube=tube_for(zz[:5],zz[5],h)
        Y=transform_jacobian(tube,zz[5],h)
        G=Y*Q
        Q1=basis(G)
        inv=Q1.inv()
        if not all(inv[a,b].is_finite() for a in range(6) for b in range(6)):
            raise ArithmeticError("noninvertible basis")
        # Taylor's formula for the reference point, on the same larger tube.
        n=9;low=jets(c[:5],c[5],n-1);remainder=jets(tube,zz[5],n)
        tail=[s(h)+h**n*r[n] for s,r in zip(low,remainder)]+[c[5]]
        c=[a.mid() for a in tail]
        shift=arb_mat([[(a-d)/s] for a,d,s in zip(tail,c,scale)])
        ne=inv*shift+(inv*G)*err
        err=arb_mat([[arb(0,abs(ne[j,0]).upper())] for j in range(6)])
        Q=Q1
    return found


def main():
    inputs=json.loads((here/"edge3_intervals.json").read_bytes())
    report=[]
    assert len(inputs)==2
    for row,r in zip(inputs,(28,30)):
        points={}
        for sg in (1,-1):
            times=[s for s in row["times"] if sg*s>=0]
            points.update(evolve(row["center"],times,arb(1)/2**r,den=512))
        ds=[cross(points[row["times"][i]],points[row["times"][(i+1)%3]]) for i in range(3)]
        if not all(d>arb(1)/256 for d in ds):raise ArithmeticError("determinant not certified")
        def endpoint(x):
            m,e=x.man_exp()
            return [str(m),int(e)]
        rec=dict(row,radius=f"2^-{r}",cross_product_bounds_dyadic=[
            [endpoint(d.lower()),endpoint(d.upper())] for d in ds],
            strict_lower_bound="1/256",signed_step="1/512",precision=ctx.prec)
        report.append(rec)
        print("verified",r,flush=True)
    (here/"edge3_certificates.json").write_text(json.dumps(report,indent=2)+"\n")

if __name__=="__main__":main()
