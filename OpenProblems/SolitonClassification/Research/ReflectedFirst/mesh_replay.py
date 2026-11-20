"""Mirror the integer TaylorStep.lean for the three initial-value boxes."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json

M = 10**28
N = 20
PAD = 10**9
ZERO = (0, 0)
ONE = (M, 1)
T = Q("5.70216430671656")
BC = Q("0.719266732593")
R = Q("0.00000001")
STEPS = 740
H = T/STEPS

def ofq(x):
    return (x.numerator*M//x.denominator, 1)

def add(a,b):
    return a[0]+b[0],a[1]+b[1]

def neg(a):
    return -a[0],a[1]

def divn(a,n):
    return a[0]//n, -((-a[1])//n)+1

def mul(a,b):
    c,r=a
    d,w=b
    return c*d//M, -((-(abs(c)*w+abs(d)*r+r*w))//M)+1

def conv(x,y,n):
    c=r=0
    for j in range(n+1):
        v,w=mul(x[j],y[n-j])
        c+=v
        r+=w
    return c,r

def advance(z):
    cs=[[a] for a in z]
    k,v,p,q,w,t=cs
    sq=[]
    for n in range(N):
        sq.append(conv(k,k,n))
        kp,kq=conv(k,p,n),conv(k,q,n)
        f=[(8*v[n][0],8*v[n][1]),
           neg(add(divn(conv(sq,k,n),16),add(divn(p[n],8),divn(conv(w,q,n),8)))),
           neg(kq),add(ONE if n==0 else ZERO,kp),ZERO,k[n]]
        for col,x in zip(cs,f):
            col.append(divn(x,n+1))
    out=[]
    for col in cs:
        u=ZERO
        for x in col[::-1]:
            u=add(x,mul(ofq(H),u))
        out.append((u[0],u[1]+PAD))
    return out

def initial(label):
    z=[ZERO]*6
    b=BC+{'minus':-R,'plus':R,'all':Q(0)}[label]
    c,r=ofq(b/8)
    z[1]=(c,r+(int(M*R/8) if label=='all' else 0))
    return z

def check_row(z):
    lim=[Q(407,50),Q(33,8),Q(731,100),Q(731,100),Q(1,100)]
    return all(abs(c)+r<=v*M for (c,r),v in zip(z,lim))

def replay(label,nsteps):
    z=initial(label)
    path=[z]
    for j in range(nsteps):
        assert check_row(z),(label,j,z)
        z=advance(z)
        path.append(z)
    return path

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--steps', type=int, default=STEPS)
    parser.add_argument('--traces', action='store_true')
    args=parser.parse_args()
    out={}
    here=Path(__file__).resolve().parent
    for label in ['minus','all','plus']:
        path=replay(label,args.steps)
        z=path[-1]
        out[label]=z
        print(label,[(c/M,r/M) for c,r in z],flush=True)
        if args.traces:
            (here/(label+'.json')).write_text(json.dumps(path,separators=(',',':')))
    if args.steps==STEPS:
        for label in ['minus','plus']:
            z=out[label]
            assert 8*(abs(z[1][0])+z[1][1]) < 4*10**20
            assert (z[3][0] if label=='plus' else -z[3][0])-z[3][1] > 18*10**19
        z=out['all']
        assert 8*(abs(z[1][0])+z[1][1])<M//100
        (here/'mesh_endpoints.json').write_text(json.dumps(out,indent=2)+'\n')
