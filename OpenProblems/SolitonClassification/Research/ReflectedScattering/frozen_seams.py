"""Validated integration of two fixed, rational seam states of the frozen ODE."""
from pathlib import Path
import json
import sys

here = Path(__file__).resolve().parent
from flint import arb, arb_poly, ctx

def field(z):
    k,v,p,q = z
    return v,-k*k*k/2-p,-k*q,k*p

def tube(z,h):
    width = [2*h*abs(j).upper()+arb(1)/64 for j in field(z)]
    for _ in range(25):
        box = [j+arb(0,r.upper()) for j,r in zip(z,width)]
        req = [h*abs(j).upper() for j in field(box)]
        if all(x<y for x,y in zip(req,width)):
            return box
        width = [r if x<r else 2*x+arb(1)/64 for x,r in zip(req,width)]
    raise ArithmeticError("A-priori enclosure failed")

def jets(z,n):
    k,v,p,q = polys = [arb_poly([j]) for j in z]
    for i in range(n):
        row = v[i],-(k*k*k)[i]/2-p[i],-(k*q)[i],(k*p)[i]
        for poly,c in zip(polys,row):
            poly[i+1] = c/(i+1)
    return polys

def integrate(k0):
    n,order = 2048,38
    h = arb(20)/n
    power = h**order
    z = [k0,arb(0),arb(1),arb(0)]
    for _ in range(n):
        box=tube(z,h)
        centre,rem = jets(z,order-1),jets(box,order)
        z=[a(h)+power*b[order] for a,b in zip(centre,rem)]
    k,v,p,q=z
    k2=k*k/2
    A=(k2*k2+v*v).sqrt()
    radial= k2*q+v*p
    transverse=k2*p-v*q
    eta,zeta=radial/A,transverse/A
    U,w=k/A.sqrt(),v/A
    psi=U*U*U*(eta*eta-zeta*zeta/2)/6-U*w*eta*zeta/2
    I=transverse/A.sqrt()
    J=I-psi/A
    assert -radial>11 and A>11
    if k0<0:
        assert -arb(10)/100<J and J< -arb(9)/100 and abs(I)<arb(1)/4
    else:
        assert J>arb(8)/10
    return dict(initial_k=k0.str(20),initial_v=0,initial_p=1,initial_q=0,
                terminal_s=20,steps=n,taylor_order=order,precision_bits=ctx.prec,
                terminal_state=[x.str(25) for x in z],
                amplitude=A.str(25),minus_radial=(-radial).str(25),
                impact=I.str(25),corrected_impact=J.str(25))

if __name__=="__main__":
    ctx.prec=512
    if len(sys.argv)!=2 or sys.argv[1] not in {"negative","positive"}:
        raise SystemExit("Choose negative or positive")
    case=sys.argv[1]
    rec=integrate(-arb(1)/4 if case=="negative" else arb(1))
    (here/(case+"_seam.json")).write_text(json.dumps(rec,indent=2)+"\n",encoding="utf8")
    print(rec["minus_radial"],rec["corrected_impact"])
