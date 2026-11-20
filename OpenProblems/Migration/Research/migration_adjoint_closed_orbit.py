"""Enclose the pure-expander (L*1,L*(|x|^2/2)) on an actual certified orbit."""
import argparse
import hashlib
import json
import re
from pathlib import Path

from flint import arb, ctx, fmpq


def series(state, degree):
    k,v,p,q = [[x] for x in state]
    k2 = []
    for n in range(degree):
        k2.append(sum(k[i]*k[n-i] for i in range(n+1)))
        k3n = sum(k2[i]*k[n-i] for i in range(n+1))
        kp = sum(k[i]*p[n-i] for i in range(n+1))
        kq = sum(k[i]*q[n-i] for i in range(n+1))
        k.append(v[n]/(n+1))
        v.append((-k3n/2-p[n])/(n+1))
        p.append(-kq/(n+1))
        q.append((int(n==0)+kp)/(n+1))
    return (k,v,p,q)


def fields(z):
    k,v,p,q=z
    return (v,-k**3/2-p,-k*q,1+k*p)


def step(z,h,n):
    tube = [u+arb(0,1) for u in z]
    domain = arb(h/2,h/2)
    for u,t,d in zip(z,tube,fields(tube)):
        assert t.contains_interior(u+domain*d), (u,t,d)
    low = series(z,n-1)
    high = series(tube,n)
    out = []
    for coefficients, bounds in zip(low,high):
        val=bounds[n]
        for c in reversed(coefficients):
            val=val*h+c
        out.append(val)
    return out


def densities(z):
    k,_,p,q=z
    return 2+k*p,k*k/2+2*q*q+k*p*(p*p+q*q)/2


def det(a,b):
    return a[0]*b[1]-b[0]*a[1]


def run(endpoint_source):
    ctx.prec=180
    src = endpoint_source
    data=src.read_bytes()
    digest=hashlib.sha256(data).hexdigest()
    assert digest=='f8c058e1b24b7f754eb07c33e352c98cfbfca2954734aa138d2cadb61140838f'
    txt=data.decode('utf-8-sig').split('def parameters :',1)[1].split('def endpointVectors',1)[0]
    a,k0,length = [arb(fmpq(int(n),int(d))) for n,d in re.findall(r'\((\d+)/(\d+):ℚ\)',txt)]
    delta=arb(0,arb(fmpq(1,10**28)))
    assert length+delta > arb(17)/4
    z=[k0+delta,arb(0),-(a+delta),arb(0)]
    denom=128
    h=arb(1)/denom
    n=22
    times={0:'0',denom:'1',denom*17//4:'17/4'}
    samples={}
    for i in range(max(times)+1):
        if i in times:
            samples[times[i]]=densities(z)
        if i<max(times):
            z=step(z,h,n)
    ordered=[samples[t] for t in ('0','17/4','1')]
    areas=[det(x,y) for x,y in zip(ordered,ordered[1:]+ordered[:1])]
    assert all(v>1 for v in areas),areas
    rec=dict(source_sha256=digest, root_sup_norm_radius='1e-28', normalized_lambda=1,
             taylor_step='1/128',taylor_remainder_order=n,taylor_picard_radius=1,
             precision_bits=ctx.prec,samples={t:[str(x) for x in v] for t,v in samples.items()},
             determinant_order=['0','17/4','1'],positive_determinants=[str(v) for v in areas])
    print(json.dumps(rec,indent=2))
    Path(__file__).with_suffix('.json').write_text(json.dumps(rec,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('endpoint_source',type=Path,help='path to CandidateEndpointChecks.lean of the certified CentroidEscape result')
    run(parser.parse_args().endpoint_source)
