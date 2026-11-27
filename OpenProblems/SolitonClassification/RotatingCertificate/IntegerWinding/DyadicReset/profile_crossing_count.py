"""Exact branch-and-bound exclusion of remote preimages of the primitive rotating profile.

Positions use integer interval arithmetic. Parameters are physical arclength in
units of the verified step. Intervals covering the two endpoints may extend past
the seam; their reference nodes lie inside the physical period.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import gzip
import hashlib
import json
from math import factorial
from pathlib import Path

D = 10**14
UNIT = (D, D)

def ceildiv(a, b):
    return -((-a)//b)

def fraction(x):
    return (x.numerator*D//x.denominator, ceildiv(x.numerator*D, x.denominator))

def add(a, b):
    return (a[0]+b[0], a[1]+b[1])

def neg(a):
    return (-a[1], -a[0])

def sub(a, b):
    return add(a, neg(b))

def mul(a, b):
    products = [x*y for x in a for y in b]
    return (min(products)//D, ceildiv(max(products), D))

def div(a, n):
    return (a[0]//n, ceildiv(a[1], n))

def expand(a, r):
    return (a[0]-r, a[1]+r)

def trig(theta):
    # |theta/16| <= 1 gives remainder <= 1/16! when truncating at degree 15.
    small = div(theta, 16)
    assert small[0] >= -D and small[1] <= D
    power = UNIT
    c = UNIT
    s = (0, 0)
    for n in range(1, 16):
        power = mul(power, small)
        term = div(power, factorial(n))
        if n % 4 in [2, 3]:
            term = neg(term)
        if n % 2:
            s = add(s, term)
        else:
            c = add(c, term)
    c, s = (expand(w, ceildiv(D, factorial(16))) for w in (c,s))
    for _ in range(4):
        c, s = sub(mul(c,c), mul(s,s)), add(mul(s,c), mul(s,c))
    return c,s

def read_arm(path):
    plain = gzip.decompress(path.read_bytes()).replace(b'\r\n', b'\n')
    lines = plain.splitlines()
    header = json.loads(lines[0])
    assert int(header['D']) == 2**240 and len(lines) == 4002
    h = F(header['h'])
    positions = []
    for i, line in enumerate(lines[1:]):
        entry = json.loads(line)
        row = entry[2] if i else entry
        # Prefix transport gives the actual value within 5e-26 of each
        # rational grid value at every strictly interior reference node.
        p,q,theta = [expand(fraction(F(row[j], 2**240)),1) for j in (2,3,5)]
        co,si = trig(theta)
        xy = (sub(mul(q,co), mul(p,si)), add(mul(q,si), mul(p,co)))
        assert all(v[1]-v[0] < D//10**7 for v in xy)
        positions.append(xy)
    return h, positions, hashlib.sha256(plain).hexdigest()

def check(base):
    h, plus, p_hash = read_arm(base/'plus4000.jsonl.gz')
    hm, minus, m_hash = read_arm(base/'minus4000.jsonl.gz')
    assert 0<h<F(1,125) and hm == -h and plus[0] == minus[0]
    assert p_hash == '792eb4d79ae72c3a406ec8d89c4289458c37c3c681ad0c1976da73b76a81667e'
    # The closing cube gives |T-4000*h| <= 1e-30.
    assert F(1,10**30)/h < F(1,1000)
    charts = [((1807,1815),(2204,2212)), ((1684,1692),(2395,2403))]
    counts = Counter()
    pending = []
    used = set()
    paths = []

    def tag(code):
        paths.append(code)
        counts[code] += 1

    @lru_cache(None)
    def box(a,b):
        j = max(-3999,min(3999,(a+b)//2))
        used.add(j)
        xy = (minus if j<0 else plus)[abs(j)]
        r = ceildiv(max(j-a,b-j)*h.numerator*D, h.denominator)
        # Unit speed along the actual curve bounds each coordinate displacement.
        return tuple(expand(v,r) for v in xy)

    def recurse(a,b,c,d):
        # All pairs with first parameter <= second are considered.
        if a>d:
            tag('reverse')
            return
        if d-a<=32 or c-b>=7970:
            tag('short')
            return
        if a==c and b==d:
            mid = (a+b)//2
            tag('square')
            recurse(a,mid,a,mid)
            recurse(a,mid,mid,b)
            recurse(mid,b,mid,b)
            return
        for k,(u,v) in enumerate(charts):
            if u[0]<=a and b<=u[1] and v[0]<=c and d<=v[1]:
                tag('chart'+str(k))
                return
        xy = box(a,b)
        zw = box(c,d)
        for j in (0,1):
            if xy[j][1] < zw[j][0] or zw[j][1] < xy[j][0]:
                tag('split_xy'+str(j))
                return
        if b-a==d-c==1:
            # The true arc is within (10 h^2)/8 of its affine interpolant
            # in each coordinate, by the second derivative bound.
            if max(abs(x) for x in (a,b,c,d))<=3999:
                e = ceildiv(10*h.numerator**2*D, 8*h.denominator**2)
                points = [box(j,j) for j in (a,b,c,d)]
                directions = [(1,0),(0,1)]
                for P,Q in [points[:2],points[2:]]:
                    tu,tv = [Q[n][0]-P[n][0] for n in (0,1)]
                    directions.append((-tv,tu))
                for nu,nv in directions:
                    def projection(P):
                        x,y = P
                        X = sorted(nu*v for v in x)
                        Y = sorted(nv*v for v in y)
                        return X[0]+Y[0],X[1]+Y[1]
                    px = [projection(P) for P in points]
                    loss = 2*(abs(nu)+abs(nv))*e
                    if max(i[1] for i in px[:2])+loss<min(i[0] for i in px[2:]) or max(i[1] for i in px[2:])+loss<min(i[0] for i in px[:2]):
                        tag('chords')
                        return
            pending.append((a,b,c,d))
            tag('undecided')
            return
        if b-a>=d-c:
            mid=(a+b)//2
            tag('first')
            recurse(a,mid,c,d)
            recurse(mid,b,c,d)
        else:
            mid=(c+d)//2
            tag('second')
            recurse(a,b,c,mid)
            recurse(a,b,mid,d)
    recurse(-4001,4001,-4001,4001)
    result = dict(counts=dict(counts),reference_nodes=len(used),
                  decision_sha256=hashlib.sha256(' '.join(paths).encode()).hexdigest(),
                  grid_hashes=[p_hash,m_hash], unresolved=pending[:50])
    return result

if __name__ == '__main__':
    result = check(Path(__file__).resolve().parent)
    print(json.dumps(result,indent=2))
    assert not result['unresolved']

