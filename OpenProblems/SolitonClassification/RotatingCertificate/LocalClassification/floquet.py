"""Outward exact rational interval signs for the multipliers of the true support return."""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import hashlib, json

here = Path(__file__).resolve().parent
old = here.parent / "classification_odd_branch_interval"

def interval(s):
    if "+/-" not in s:
        return Q(s), Q(s)
    a,b = s.strip("[]").split("+/-")
    m,r = Q(a.strip() or "0"), Q(b.strip())
    return m-r,m+r

def add(a,b):
    return a[0]+b[0],a[1]+b[1]

def mul(a,b):
    x=[i*j for i in a for j in b]
    return min(x),max(x)

def determinant(m):
    out=(Q(0),Q(0))
    for p in permutations(range(4)):
        sign=(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
        term=(Q(sign),Q(sign))
        for i,j in enumerate(p):
            term=mul(term,m[i][j])
        out=add(out,term)
    return out

def main():
    cert=json.loads((old/"shooting_certificate.json").read_bytes())
    K,I,L,H,T=2000,4000,17,4,32
    r=Q(1,10**32)
    # Uniform center-to-parameter change in D_z Phi at the variable endpoint.
    first=4*K
    second=T*first*(4*I)*H*first**2
    eps=Q(1,10**12)
    sides=[]
    hashes={}
    for index,sgn in enumerate(("plus","minus")):
        path=old/f"metric_{sgn}_o60_n4000.json"
        hashes[sgn]=hashlib.sha256(path.read_bytes()).hexdigest()
        assert cert["inputs"][index]["sha256"]==hashes[sgn]
        d=interval(cert["metric_checks"][index]["fundamental_endpoint_error"])[1]
        assert d+(second+L*first)*r < eps
        vals=json.loads(path.read_bytes())["endpoint_fundamental"]
        sides.append([[add(interval(v),(-eps,eps)) for v in row[:4]] for row in vals[:4]])
    plus,minus=sides
    # For each open interval the opposite, separately certified signs
    # give a real eigenvalue. Time translation gives the fourth eigenvalue +1.
    samples=[-3,-2,Q(-1,100),Q(-1,1000),100,110]
    results={}
    for x in samples:
        d=determinant([[add(plus[i][j],mul((-x,-x),minus[i][j])) for j in range(4)] for i in range(4)])
        # Signs are read from det(plus−x minus), a monic-up-to-positive-factor quartic.
        got=1 if d[0]>0 else -1 if d[1]<0 else 0
        results[str(x)] = [d[0].numerator//d[0].denominator, -((-d[1].numerator)//d[1].denominator),got]
        assert got!=0
    for lo,hi in [(-3,-2),(Q(-1,100),Q(-1,1000)),(100,110)]:
        assert results[str(lo)][2]==-results[str(hi)][2]
    target=here/"FloquetChecks.json"
    target.write_text(json.dumps(dict(input_sha256=hashes,entry_inflation=str(eps),
        integer_outer_determinant_bounds_and_sign=results,root_intervals=[["-3","-2"],["-1/100","-1/1000"],["100","110"]],
        neutral_root="1, exactly, by autonomous tangent"),indent=2)+"\n")
    print(results)

if __name__=="__main__":
    main()
