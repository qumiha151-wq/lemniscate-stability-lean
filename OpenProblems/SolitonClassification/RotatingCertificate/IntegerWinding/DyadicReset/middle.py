"""Emit an independently kernel-replayable residual for a genuine midpoint reset."""
from reset_tape import *
def generate():
    idx=2000
    with gzip.open(HERE/'plus4000.jsonl.gz','rt',encoding='utf8') as fp:
        header=json.loads(next(fp))
        for i in range(idx+2):
            cell=json.loads(next(fp))
            if i==idx:
                node=cell[2]
            if i==idx+1:
                expect=cell
    h=seed(1)[1]
    polys=path(node,h)
    sx,sm,den=defects(polys,h)
    assert expect==[sx,sm,[sum(p) for p in polys]]
    literal=lambda x:'['+','.join(str(a) for a in x)+']'
    data="\n".join("def a"+str(i)+" : List ℤ := "+literal(p) for i,p in enumerate(polys))
    end=literal(expect[2])
    source = """import Mathlib.Tactic.FinCases
import SolitonClassification.Rotating.MaskedResetDigits
namespace SolitonClassification.Rotating.DyadicReset.Middle
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def den : ℤ := 2^240
def halfBase : ℤ := 2^1279
def hn : ℤ := HNUM
def hd : ℤ := HDEN
DATA
def rows : Array (List ℤ) := #[a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30]
def X (i : Nat) := pack (2*halfBase) (rows[i]?.getD [])
def dx (i : Nat) := pack (2*halfBase) (((rows[i]?.getD []).drop 1).zipIdx.map
  (fun (c,j) => ((j+1:Nat):ℤ)*c))
def field (i : Nat) : ℤ := Id.run do
  let d := den
  let k := X 0
  let u := X 1
  let p := X 2
  let q := X 3
  let b := X 4
  if i<6 then
    return (#[128*d^2*u,-k^3-2*d^2*p-2*d*b*q,-16*d*k*q,
      16*d^3+16*d*k*p,0,16*d^2*k]:Array ℤ)[i]?.getD 0
  let j := (i-6)/5
  let s := 6+5*j
  let sk := X s
  let su := X (s+1)
  let sp := X (s+2)
  let sq := X (s+3)
  return (#[128*d^2*su,-3*k^2*sk-2*d^2*sp-2*d*b*sq-(if j=4 then 2*d^2*q else 0),
    -16*d*(q*sk+k*sq),16*d*(p*sk+k*sp),16*d^2*sk]:Array ℤ)[(i-6)%5]?.getD 0
def residual (i : Nat) : Nat :=
  l1 (extract halfBase 157 (16*hd*den^2*dx i-hn*field i))
def commonDen : ℤ := 16*hd*den^3
def repunit : ℤ := ((2*halfBase)^157-1)/(2*halfBase-1)
def laneOffset : ℤ := 2^748
def mask : ℕ := ((2*laneOffset-1)*repunit).toNat
def good (i : Nat) := Id.run do
  let biased := 16*hd*den^2*dx i-hn*field i+laneOffset*repunit
  return decide (0≤biased ∧ (biased.toNat &&& mask)=biased.toNat)
theorem scalar_budget : (157:ℤ)*laneOffset*10^64≤commonDen := by decide +kernel
theorem rep_correct : repunit=pack (2*halfBase) (List.replicate 157 1) := by decide +kernel
theorem mask_capacity : ((digits 1280 157 mask).all (fun j => decide (j≤2*laneOffset.toNat)))=true ∧
    mask < ((2:ℕ)^1280)^157 := by decide +kernel
theorem good_sound (i : Nat) (pass : good i=true) :
    (residual i : ℤ)*10^64 ≤ commonDen := by
  let v := 16*hd*den^2*dx i-hn*field i
  let t := v+laneOffset*repunit
  have checks : 0≤t ∧ (t.toNat &&& mask)=t.toNat := of_decide_eq_true pass
  have high : t.toNat < ((2:ℕ)^1280)^157 := (checks.2.symm.le.trans Nat.and_le_right).trans_lt mask_capacity.2
  have val : (t.toNat:ℤ)=t := Int.toNat_of_nonneg checks.1
  have ot : (laneOffset.toNat:ℤ)=laneOffset := by decide +kernel
  have radix : v=(t.toNat:ℤ)-laneOffset.toNat*pack (2*halfBase) (List.replicate 157 1) := by
    rw [val,ot,←rep_correct]; dsimp only [t]; ring
  have bd := mask_l1 (w:=1280) (k:=halfBase) (L:=laneOffset.toNat)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    high radix checks.2 (fun a ha=>of_decide_eq_true (List.all_eq_true.mp mask_capacity.1 a ha))
  change (l1 (extract halfBase 157 v):ℤ)*10^64≤commonDen
  apply le_trans _ scalar_budget
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  rw [←ot]
  exact_mod_cast bd

def endpoints : List ℤ := END
def magnitude : Nat := rows.foldl (fun m p => max m (l1 p)) 0
theorem magnitude_and_endpoints :
    den ≤ (magnitude:ℤ) ∧
    16*hd*den^2*52*(magnitude:ℤ)+256*hn*(magnitude:ℤ)^3 < halfBase ∧
    rows.toList.map List.sum = endpoints := by decide +kernel
THEOREMS
end SolitonClassification.Rotating.DyadicReset.Middle
#print axioms SolitonClassification.Rotating.DyadicReset.Middle.all_residuals
"""
    chunks=[]
    for i in range(31):
        chunks.append(f'theorem cell_{i} : good {i} = true := by decide +kernel')
    body='theorem all_residuals : '+' ∧ '.join(f'(residual {k}:ℤ)*10^64≤commonDen' for k in range(31))+' :=\n  ⟨'+','.join('good_sound _ cell_'+str(i) for i in range(31))+'⟩\n'
    chunks.append(body)
    source=source.replace('HNUM',str(h.numerator)).replace('HDEN',str(h.denominator)).replace('DATA',data).replace('ROWS',','.join('a'+str(i) for i in range(31))).replace('END',end).replace('THEOREMS','\n'.join(chunks).replace('\\n','\n'))
    (HERE/'WindingMiddleReset.lean').write_bytes(source.encode())
if __name__=='__main__':
    generate()
