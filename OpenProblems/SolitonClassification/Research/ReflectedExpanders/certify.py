"""Validated shooting for centrally crossing homothetic elastic expanders.

All evolution, all variational enclosures and all final inequalities use Arb
real balls. Floating-point numbers are used only for optional console output.
"""
from pathlib import Path
import argparse
import json
import sys

here = Path(__file__).resolve().parent
sys.path.insert(0, str(here.parents[1] / "pydeps"))
from flint import arb, arb_mat, arb_poly, ctx

def field(z):
    k,v,p,q,A,B,C,D = z
    return [v,-k*k*k/2-p,-k*q,1+k*p,B,-3*k*k*A/2-C,-q*A-k*D,p*A+k*C]

def jets(z, n):
    polys=[arb_poly([a]) for a in z]
    k,v,p,q,A,B,C,D=polys
    for i in range(n):
        k2=k*k
        row=(v[i],-(k2*k)[i]/2-p[i],-(k*q)[i],(k*p)[i]+int(i==0),
             B[i],-3*(k2*A)[i]/2-C[i],-(q*A)[i]-(k*D)[i],(p*A)[i]+(k*C)[i])
        for a,val in zip(polys,row):
            a[i+1]=val/(i+1)
    return polys

def cover(z,h):
    hh=abs(h).upper()
    width=[hh*abs(v).upper()*2+arb(1)/64 for v in field(z)]
    for _ in range(30):
        tube=[v+arb(0,r.upper()) for v,r in zip(z,width)]
        req=[hh*abs(v).upper() for v in field(tube)]
        if all(a<b for a,b in zip(req,width)):
            return tube
        width=[a if b<a else 2*b+arb(1)/64 for a,b in zip(width,req)]
    raise ArithmeticError("Local enclosure not proved")

def flow(b,t,steps,order):
    h=t/steps
    z=list(map(arb,[0,0,0,0,0,1,0,0]));z[1]=b
    hn=h**order
    for i in range(steps):
        try:
            box=cover(z,h)
        except ArithmeticError:
            print("Failed at step", i, [str(a) for a in z],flush=True)
            raise
        base=jets(z,order-1)
        remainder=jets(box,order)
        z=[pol(h)+hn*other[order] for pol,other in zip(base,remainder)]
    return z

def endpoint(z):
    k,v,p,q,A,B,C,D=z
    return arb_mat([[v],[q]]),arb_mat([[B,-k*k*k/2-p],[D,1+k*p]])

def enclosure(b,t0,r,steps,order):
    f,j=endpoint(flow(b,t0,steps,order))
    numerical_inverse=j.inv()
    inverse=arb_mat([[numerical_inverse[i,j].mid() for j in range(2)] for i in range(2)])
    _,jj=endpoint(flow(b+arb(0,r),t0+arb(0,r),steps,order))
    e=arb_mat([[1,0],[0,1]])-inverse*jj
    correction=inverse*f
    row_norm=[sum(abs(e[i,j]).upper() for j in range(2)) for i in range(2)]
    for i in range(2):
        assert row_norm[i] < 1, row_norm
        assert abs(correction[i,0]).upper()+r*row_norm[i]<r, (correction,row_norm,r)
    assert not inverse.det().contains(0)
    def dyadic(x):
        n,e=x.man_exp()
        return [str(n),int(e)]
    return dict(center=[b.str(50),t0.str(50)],center_dyadic=[dyadic(b),dyadic(t0)],
                inverse_dyadic=[[dyadic(inverse[i,j]) for j in range(2)] for i in range(2)],
                radius=r.str(30),steps=steps,order=order,
                precision_bits=ctx.prec,center_residual=[f[i,0].str(35) for i in range(2)],
                box_jacobian=[[jj[i,j].str(35) for j in range(2)] for i in range(2)],
                preconditioner=[[inverse[i,j].str(50) for j in range(2)] for i in range(2)],
                correction=[correction[i,0].str(35) for i in range(2)],
                contraction_row_bounds=[a.str(28) for a in row_norm])

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--b',default='0.7192667325932558')
    p.add_argument('--t',default='5.7021643067166385')
    p.add_argument('--radius',default='1e-15')
    p.add_argument('--steps',type=int,default=350)
    p.add_argument('--order',type=int,default=28)
    p.add_argument('--bits',type=int,default=256)
    p.add_argument('--refine',type=int,default=1)
    p.add_argument('--replay')
    p.add_argument('--output',default='first_certificate.json')
    args=p.parse_args();ctx.prec=args.bits
    b,t=arb(args.b).mid(),arb(args.t).mid()
    if args.replay:
        old=json.loads((here/args.replay).read_bytes())
        ctx.prec=old['precision_bits']
        b,t=[arb(int(n))*arb(2)**e for n,e in old['center_dyadic']]
        args.steps=old['steps'];args.order=old['order'];args.radius=old['radius_input']
    else:
        for _ in range(args.refine):
            f,j=endpoint(flow(b,t,args.steps,args.order))
            d=j.inv()*f
            b,t=(b-d[0,0]).mid(),(t-d[1,0]).mid()
    print("Newton center",b.str(35),t.str(35),flush=True)
    rec=enclosure(b,t,arb(args.radius),args.steps,args.order)
    rec["radius_input"]=args.radius
    print(json.dumps(rec,indent=2),flush=True)
    if args.replay:
        assert rec==old
    else:
        (here/args.output).write_text(json.dumps(rec,indent=2)+"\n",encoding="utf8")
