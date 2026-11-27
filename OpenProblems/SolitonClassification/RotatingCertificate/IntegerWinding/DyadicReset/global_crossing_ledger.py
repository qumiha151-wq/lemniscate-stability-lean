"""Build the integer reference table and subdivision proof for the full profile."""
import json
from collections import Counter
from pathlib import Path
from profile_crossing_count import D, read_arm

here=Path(__file__).resolve().parent
S=10**6
node_error=100
step_upper=7553
chord_error=600
windows=[(1807,1815,2204,2212),(1684,1692,2395,2403)]
def save(path,data):
    path.write_bytes((json.dumps(data,separators=(',',':'))+'\n').encode())

def build():
    hp,pos,ph=read_arm(here/'plus4000.jsonl.gz')
    hm,neg,mh=read_arm(here/'minus4000.jsonl.gz')
    assert hm==-hp and 0<hp and hp.numerator*S < step_upper*hp.denominator
    assert 10*step_upper**2<=chord_error*S
    used={}
    counts=Counter()
    def ref(j):
        if j not in used:
            xy=(neg if j<0 else pos)[abs(j)]
            used[j]=tuple((a+b)*S//(2*D) for a,b in xy)
        return used[j]
    def reference(a,b):
        j=max(-3999,min(3999,(a+b)//2))
        r=node_error+step_upper*max(abs(a-j),abs(b-j))
        return j,ref(j),r
    def check(a,b,c,d):
        assert a<=b and c<=d and a<=c
        if d-a<=32 or c-b>=7970:
            return ['short']
        if a==c and b==d:
            m=(a+b)//2
            return ['square',check(a,m,a,m),check(a,m,m,b),check(m,b,m,b)]
        for i,(A,B,C,E) in enumerate(windows):
            if A<=a and b<=B and C<=c and d<=E:
                return ['chart',i]
        j,x,r=reference(a,b)
        k,y,w=reference(c,d)
        for axis in (0,1):
            if abs(x[axis]-y[axis])>r+w:
                return ['axis',j,k,axis]
        if b-a==d-c==1:
            assert all(abs(j)<=3999 for j in (a,b,c,d))
            points=[ref(t) for t in (a,b,c,d)]
            directions=[(1,0),(0,1)]
            for p,q in (points[:2],points[2:]):
                directions.append((p[1]-q[1],q[0]-p[0]))
            for u,v in directions:
                values=[u*ex+v*ey for ex,ey in points]
                loss=2*(abs(u)+abs(v))*(node_error+chord_error)
                if min(values[2:])-max(values[:2])>loss or min(values[:2])-max(values[2:])>loss:
                    return ['chord',a,b,c,d,u,v]
            raise ArithmeticError((a,b,c,d))
        if b-a>=d-c:
            m=(a+b)//2
            return ['first',check(a,m,c,d),check(m,b,c,d)]
        m=(c+d)//2
        return ['second',check(a,b,c,m),check(a,b,m,d)]
    tree=check(-4001,4001,-4001,4001)
    keys=sorted(used)
    ids={j:i for i,j in enumerate(keys)}
    def label(node):
        kind,*data=node
        counts[kind]+=1
        if kind=='axis':return [kind,ids[data[0]],ids[data[1]],data[2]]
        if kind=='chord':return [kind,*[ids[j] for j in data[:4]],*data[4:]]
        if kind in ('square','first','second'):return [kind,*map(label,data)]
        return node
    ledger=label(tree)
    pts=[[j,*used[j]] for j in keys]
    save(here/'global_ref_points.json',dict(points=pts,scale=S,coordinate_error=node_error,grid_hashes=[ph,mh]))
    save(here/'global_crossing_ledger.json',dict(tree=ledger,counts=counts,root=[-4001,4001,-4001,4001]))
    lib=here/'fullassembly'/'IntegerGlobalReferences.lean'
    lib.parent.mkdir(exist_ok=True)
    src='''import SolitonClassification.Rotating.IntegerChartIntersection

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount

structure RefPoint where
  index : ℤ
  x : ℤ
  y : ℤ
  deriving DecidableEq, Repr

'''
    # Short blocks avoid deep elaboration of a four-digit array literal.
    chunks=[pts[i:i+64] for i in range(0,len(pts),64)]
    pieces=[]
    for i,block in enumerate(chunks):
        src+=f'def refs{i} : Array RefPoint := #[\n'
        src+=',\n'.join('  ⟨'+','.join(str(n) for n in row)+'⟩' for row in block)+'\n]\n'
        pieces.append(f'refs{i}')
    src+='def refPoint (i : ℕ) : RefPoint :=\n  match i/64 with\n'
    for j,part in enumerate(pieces):
        src+=f'  | {j} => {part}[i%64]?.getD ⟨0,0,0⟩\n'
    src+='  | _ => ⟨0,0,0⟩\n'
    src+='structure ReferenceTable where\n  size : ℕ\n  get : ℕ → RefPoint\n'
    src+=f'def refTable : ReferenceTable := ⟨{len(pts)},refPoint⟩\n'
    src+=f'theorem ref_count : refTable.size={len(pts)} := rfl\n'
    src+='\nend SolitonClassification.Rotating.IntegerTarget.GlobalCount\n'
    lib.write_bytes(src.encode())
    print(len(pts),dict(counts),flush=True)

if __name__=='__main__':build()

