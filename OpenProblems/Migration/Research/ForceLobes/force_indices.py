"""Certify force zeros and their intrinsic winding signs on the published orbit."""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import zlib
from flint import acb,arb,ctx

def check(folder):
    ctx.prec=140
    data=json.loads((folder/"header.json").read_bytes())
    names=("k","v","p","q")
    data["rows"]={}
    for name in names:
        text=b"".join((folder/(name+".b85")).read_bytes().split())
        data["rows"][name]=json.loads(zlib.decompress(base64.b85decode(text)))
    sha=hashlib.sha256((json.dumps(data,separators=(",",":"))+"\n").encode()).hexdigest()
    assert sha==json.loads((folder/"shape_report.json").read_bytes())["packet_sha256"]
    D=10**42
    pitch=arb(data["pitch"])/D+arb(0,"1e-28")
    M=65536
    grid=[]
    for key in names:
        co=[acb(arb(a)/D,arb(b)/D) for a,b in data["rows"][key]]
        z=co+[acb(0)]*(M-2*len(co)+1)+[v.conjugate() for v in co[:0:-1]]
        grid.append([v.real*M+arb(0,"1e-19") for v in acb.dft(z,inverse=True)])
    dt=arb(61)/M
    e=arb(0,1)
    zeros=[]
    for j in range(M):
        start=[v[j] for v in grid]
        end=[v[(j+1)%M] for v in grid]
        box=[v+90*dt*e for v in start]
        for _ in range(3):
            k,v,p,q=box
            rhs=(8*v,-k*k*k/16-(p+pitch*q)/8,-k*q,1+k*p)
            box=[v+abs(d)*dt*e for v,d in zip(start,rhs)]
        k,v,p,q=box
        F=-(p+pitch*q)
        lo=-(start[2]+pitch*start[3])
        hi=-(end[2]+pitch*end[3])
        assert not lo.contains(0) and not hi.contains(0)
        if F.contains(0):
            h=q-pitch*p
            dF=k*h-pitch
            assert not dF.contains(0),(j,"derivative")
            if (lo>0)!=(hi>0):
                assert not h.contains(0),(j,"companion")
                assert (dF>0)==(hi>0)
                zeros.append([j,1 if h>0 else -1,1 if dF>0 else -1])
        else:assert (lo>0)==(hi>0)
    counts={f"companion{h:+d}_crossing{e:+d}":sum(x[1:]==[h,e] for x in zeros)
            for h in (-1,1) for e in (-1,1)}
    defect=sum(x[2] for x in zeros if x[1]>0)
    return dict(fourier_sha256=sha,grid=M,force_zeros=zeros,counts=counts,
                total_force_sign_changes=len(zeros),relative_degree=defect,
                tangent_turning=-1,center_winding=-1-defect)
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("fourier",type=Path)
    p.add_argument("--out",type=Path)
    a=p.parse_args();report=check(a.fourier)
    print(report["total_force_sign_changes"],report["counts"],report["center_winding"])
    if a.out:a.out.write_text(json.dumps(report,indent=2)+"\n","utf8")
