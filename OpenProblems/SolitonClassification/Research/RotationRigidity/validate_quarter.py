"""Validated quarter-orbit derivatives throughout an existing reflected-root box.

Arb's Taylor polynomial/remainder and the strict Picard tube enclose all
trajectories throughout the box. The four columns are k0, p0, v0 and pitch.
"""
from pathlib import Path
import argparse
import hashlib
import json

here = Path(__file__).resolve().parent
from flint import arb, arb_mat, arb_poly, ctx

def field(z):
    k,v,p,q=z[:4]
    f=[v,-k*k*k/2-p,-k*q,1+k*p]
    for col in range(4):
        A,D,U,V=z[4+4*col:8+4*col]
        f.extend([D,-3*k*k*A/2-U-(q if col==3 else 0),-q*A-k*V,p*A+k*U])
    return f

def tube(z,h):
    width=[h*abs(v).upper()*2+arb(1)/64 for v in field(z)]
    for _ in range(30):
        box=[v+arb(0,r.upper()) for v,r in zip(z,width)]
        req=[h*abs(v).upper() for v in field(box)]
        if all(a<b for a,b in zip(req,width)):
            return box
        width=[a if b<a else 2*b+arb(1)/64 for a,b in zip(width,req)]
    raise ArithmeticError("Picard tube failed")

def jets(z,order):
    a=[arb_poly([v]) for v in z]
    k,v,p,q=a[:4]
    for n in range(order):
        k2=k*k
        row=[v[n],-(k2*k)[n]/2-p[n],-(k*q)[n],(k*p)[n]+int(n==0)]
        for col in range(4):
            A,D,U,V=a[4+4*col:8+4*col]
            row.extend([D[n],-3*(k2*A)[n]/2-U[n]-(q[n] if col==3 else 0),
                        -(q*A)[n]-(k*V)[n],(p*A)[n]+(k*U)[n]])
        for poly,val in zip(a,row):
            poly[n+1]=val/(n+1)
    return a

case_names=("seventh","third","first","fifth","sixth","second","fourth","eighth","ninth","tenth","eleventh","twelfth")

def run(name, source, write):
    o=json.loads(source.read_bytes())["cases"][case_names.index(name)]
    ctx.prec=o["precision_bits"]
    radius=arb(o["radius_input"])
    b,t=[arb(int(n))*arb(2)**e+arb(0,radius.upper()) for n,e in o["center_dyadic"]]
    steps,order=o["steps"],o["order"]
    h=t/steps
    hn=h**order
    z=list(map(arb,[0,0,0,0,1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0]))
    z[1]=b
    for _ in range(steps):
        box=tube(z,abs(h).upper())
        base=jets(z,order-1)
        tail=jets(box,order)
        z=[a(h)+hn*b[order] for a,b in zip(base,tail)]
    k,v,p,q=z[:4]
    det_even=z[4]*z[10]-z[8]*z[6]
    det_split=z[12]*z[18]-z[16]*z[14]
    acc=-k**3/2-p
    assert not acc.contains(0), acc
    assert not det_even.contains(0),det_even
    assert not det_split.contains(0),det_split
    data={"base_case":case_names.index(name),"base_case_sha256":hashlib.sha256(json.dumps(o,sort_keys=True,separators=(",",":")).encode("utf8")).hexdigest(),
          "precision_bits":ctx.prec,"steps":steps,"order":order,"centre_marker_box":b.str(25),
          "quarter_time_box":t.str(25),"terminal_curvature":k.str(25),
          "terminal_normal_support":p.str(25),"seam_acceleration":acc.str(25),
          "even_minor":det_even.str(25),"centre_pitch_minor":det_split.str(25),
          "projected_matrix":[[z[j+i].str(25) for j in (4,8,12,16)] for i in (0,2)]}
    # At the root v=q=0. Autonomy gives the missing initial q column:
    # M (b e_k+e_q) = (0,acc,0,1+k*p). Unit determinant follows from div f=0.
    end_flow=[arb(0),acc,arb(0),1+k*p]
    m=arb_mat([[z[4+r],z[12+r],z[8+r],end_flow[r]-b*z[4+r]] for r in range(4)])
    # Cofactors give the v row of M^-1 without wrapping in interval division.
    row=[(-1)**(j+1)*arb_mat([[m[r,c] for c in (0,2,3)] for r in range(4) if r!=j]).det()
         for j in range(4)]
    tr=2*sum(row[j]*(1,-1,1,-1)[j]*m[j,1] for j in range(4))
    data["half_return_trace"]=tr.str(25)
    data["fundamental_matrix"]=[[m[i,j].str(25) for j in range(4)] for i in range(4)]
    if not abs(tr).lower()>2:
        raise ArithmeticError(f"Transverse hyperbolicity unproved at {name}: {tr}")
    data["nonresonance"]="all covers"
    path=here/(name+"_odd_rank.json")
    if write:
        path.write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    elif json.loads(path.read_bytes())!=data:
        raise ArithmeticError(f"Recomputed record differs: {path}")
    print(name, data["seam_acceleration"],data["even_minor"],data["centre_pitch_minor"],flush=True)

if __name__=="__main__":
    if not __debug__:
        raise SystemExit("Use Python without -O so that all strict inequalities are checked.")
    a=argparse.ArgumentParser()
    a.add_argument("name",nargs="*")
    published=here.parent/"ReflectedExpanders"/"certificates.json"
    a.add_argument("--base-cases",type=Path,default=published)
    a.add_argument("--write",action="store_true")
    args=a.parse_args()
    for name in args.name or case_names:
        run(name,args.base_cases,args.write)
