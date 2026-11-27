"""Dyadic polynomial paths and exact defects for the genuine winding-one seed.

A local normalized variable z in [0,1] keeps all coefficients small.
The proposed path may be computed approximately: only the independent
polynomial-defect calculation below supplies its certificate. No Arb needed.
"""
import argparse
from fractions import Fraction as Q
import gzip
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
D = 1 << 240
DEG = 52
BITS = 1280
BASE = 1 << BITS
HALF = BASE >> 1
MASK = BASE - 1
ROWS = (0, 1, 2, 3, 5)


def round_div(a, b):
    return (a+b//2)//b


def seed(sign):
    original = HERE.parent/'center.json'
    if not original.is_file():
        original = HERE.parent/'primitive_rotating_winding/center.json'
    raw = json.loads(original.read_bytes())
    k, p, half, alpha, beta = map(Q, raw['center'])
    e, g = map(Q, raw['phase'])
    x = [k, alpha*e/8, p, alpha*g, beta, Q(0)]
    s = [round(c*D) for c in x]
    s.extend(D*int(i == j) for j in range(5) for i in ROWS)
    return s, sign*half/4000


def path(node, h):
    polys = [[a] for a in node]
    k, u, p, q, beta, theta = polys[:6]
    square = []
    for n in range(DEG):
        def conv(a, b):
            return round_div(sum(ai*bi for ai, bi in zip(a, reversed(b))), D)
        square.append(conv(k, k))
        ds = [128*u[n], -conv(square,k)-2*p[n]-2*round_div(beta[0]*q[n],D),
              -16*conv(k,q), 16*(D*int(n==0)+conv(k,p)), 0, 16*k[n]]
        for j in range(5):
            sk,su,sp,sq,st = polys[6+5*j:11+5*j]
            ds.extend([128*su[n],-3*conv(square,sk)-2*sp[n]
                       -2*round_div(beta[0]*sq[n],D)-2*q[n]*int(j==4),
                       -16*(conv(q,sk)+conv(k,sq)),16*(conv(p,sk)+conv(k,sp)),16*sk[n]])
        denom = h.denominator*16*(n+1)
        for coeffs, a in zip(polys,ds):
            coeffs.append(round_div(h.numerator*a,denom))
    return polys


def pack(seq):
    return sum(int(a) << (j*BITS) for j,a in enumerate(seq))


def unpack_l1(value, degree):
    total = 0
    for _ in range(degree+1):
        a = ((value+HALF) & MASK)-HALF
        total += abs(a)
        value = (value-a) >> BITS
    assert value == 0
    return total


def defects(polys,h):
    # Each exact polynomial residual is (16*h.denominator*D^3) times
    # [d_z P - h*field(P)]. Coefficients are integers. The bound below
    # prevents carries in the balanced-base convolution representation.
    magnitude=max(sum(map(abs,row)) for row in polys)
    assert magnitude >= D
    den = 16*h.denominator*D**3
    bound = 16*h.denominator*D*D*DEG*magnitude + 256*abs(h.numerator)*magnitude**3
    assert bound < HALF
    val=[pack(row) for row in polys]
    slope=[pack([j*a for j,a in enumerate(row) if j])*(den//D) for row in polys]
    k,u,p,q,b,_=val[:6]
    ds=[128*D**2*u,-k**3-2*D**2*p-2*D*b*q,-16*D*k*q,
        16*D**3+16*D*k*p,0,16*D**2*k]
    for j in range(5):
        sk,su,sp,sq,st=val[6+5*j:11+5*j]
        ds.extend([128*D**2*su,-3*k*k*sk-2*D**2*sp-2*D*b*sq-2*D**2*q*int(j==4),
                   -16*D*(q*sk+k*sq),16*D*(p*sk+k*sp),16*D**2*sk])
    norms=[unpack_l1(y-h.numerator*f,3*DEG) for y,f in zip(slope,ds)]
    state=max(norms[:6])
    matrix=max(sum(norms[6+5*j+i] for j in range(5)) for i in range(5))
    return state,matrix,den


def run(sign,count):
    target=HERE/f"{'plus' if sign>0 else 'minus'}{count}.jsonl.gz"
    node,h=seed(sign)
    sx=sm=0
    start=time.perf_counter()
    with gzip.open(target,'wt',encoding='utf8') as fp:
        fp.write(json.dumps(dict(D=str(D),degree=DEG,h=str(h),sign=sign))+'\n')
        fp.write(json.dumps(node)+'\n')
        for step in range(count):
            polys=path(node,h)
            x,m,den=defects(polys,h)
            sx=max(sx,x);sm=max(sm,m)
            node=[sum(poly) for poly in polys]
            fp.write(json.dumps([x,m,node],separators=(',',':'))+'\n')
            if not (step+1)%100:
                fp.flush()
                print('checked',sign,step+1,round(time.perf_counter()-start,2),flush=True)
    print(json.dumps(dict(sign=sign,count=count,seconds=time.perf_counter()-start,
                          state_defect_upper=str(Q(sx,den)),
                          matrix_defect_upper=str(Q(sm,den)),
                          state_float_upper=float(Q(sx,den)),
                          matrix_float_upper=float(Q(sm,den)),path=str(target))),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('sign',type=int,choices=[-1,1])
    parser.add_argument('count',type=int)
    args=parser.parse_args()
    run(args.sign,args.count)
