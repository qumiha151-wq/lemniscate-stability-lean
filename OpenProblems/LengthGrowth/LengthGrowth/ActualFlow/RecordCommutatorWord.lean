import LengthGrowth.ActualFlow.RecordSweptAreaDuration

/-! Exact evaluation of a five-letter iterated integral of a zero-winding
commutator of two planar squares. The updates integrate the triangular prefix
system along one segment. -/
noncomputable section
namespace LengthGrowth.RecordCommutator

structure Prefix (R : Type*) where
  x : R
  xx : R
  xxy : R
  xxyx : R
  xxyxy : R
  deriving DecidableEq

/-- Prefix integrals of the word xxyxy after a segment of displacement (p,q).
The empty-prefix integral is one. -/
def step {R : Type*} [Field R] (v : Prefix R) (p q : R) : Prefix R :=
  ⟨v.x+p, v.xx+p*v.x+p^2/2,
    v.xxy+q*v.xx+p*q/2*v.x+p^2*q/6,
    v.xxyx+p*v.xxy+p*q/2*v.xx+p^2*q/6*v.x+p^3*q/24,
    v.xxyxy+q*v.xxyx+p*q/2*v.xxy+p*q^2/6*v.xx+p^2*q^2/24*v.x+p^3*q^2/120⟩

def squareA : List (ℚ×ℚ) := [(1,0),(0,1),(-1,0),(0,-1)]
def squareB : List (ℚ×ℚ) := [(-1,0),(0,-1),(1,0),(0,1)]
def returnEdges (e : List (ℚ×ℚ)) := e.reverse.map (fun p=>(-p.1,-p.2))
def commutator := squareA++squareB++returnEdges squareA++returnEdges squareB
def prefixes (e : List (ℚ×ℚ)) : Prefix ℚ :=
  e.foldl (fun v d => step v d.1 d.2) ⟨0,0,0,0,0⟩

/-- The signed area and the lower displayed prefixes cancel. The degree-five
coefficient detects the order in which the oppositely oriented pieces occur. -/
theorem commutator_coefficient : prefixes commutator=⟨0,0,0,0,1⟩ := by
  norm_num [prefixes,commutator,returnEdges,squareA,squareB,List.foldl,step]

/-- Along a straight segment, these polynomials satisfy the defining
recursion dI_(wi)=I_w dX_i for every nonempty prefix of xxyxy. -/
theorem step_derivatives (v : Prefix ℝ) (p q s : ℝ) :
    let w:=fun u:ℝ => step v (u*p) (u*q)
    HasDerivAt (fun u=>(w u).x) p s ∧
    HasDerivAt (fun u=>(w u).xx) ((w s).x*p) s ∧
    HasDerivAt (fun u=>(w u).xxy) ((w s).xx*q) s ∧
    HasDerivAt (fun u=>(w u).xxyx) ((w s).xxy*p) s ∧
    HasDerivAt (fun u=>(w u).xxyxy) ((w s).xxyx*q) s := by
  dsimp [step]
  have hp : HasDerivAt (fun u:ℝ=>u*p) p s := by simpa using (hasDerivAt_id s).mul_const p
  have hq : HasDerivAt (fun u:ℝ=>u*q) q s := by simpa using (hasDerivAt_id s).mul_const q
  have hpq := (hp.mul hq).div_const (2:ℝ)
  have hppq := ((hp.pow 2).mul hq).div_const (6:ℝ)
  have hpqq := (hp.mul (hq.pow 2)).div_const (6:ℝ)
  have hpppq := ((hp.pow 3).mul hq).div_const (24:ℝ)
  have hppqq := ((hp.pow 2).mul (hq.pow 2)).div_const (24:ℝ)
  have hpppqq := ((hp.pow 3).mul (hq.pow 2)).div_const (120:ℝ)
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply ((hasDerivAt_const s v.x).add hp).congr_deriv
    ring
  · have first := (hasDerivAt_const s v.xx).add (hp.mul_const v.x)
    apply (first.add ((hp.pow 2).div_const (2:ℝ))).congr_deriv
    ring
  · have first := (hasDerivAt_const s v.xxy).add (hq.mul_const v.xx)
    apply ((first.add (hpq.mul_const v.x)).add hppq).congr_deriv
    simp only [Pi.pow_apply]
    ring
  · have first := (hasDerivAt_const s v.xxyx).add (hp.mul_const v.xxy)
    have middle := (first.add (hpq.mul_const v.xx)).add (hppq.mul_const v.x)
    apply (middle.add hpppq).congr_deriv
    simp only [Pi.pow_apply]
    ring
  · have first := (hasDerivAt_const s v.xxyxy).add (hq.mul_const v.xxyx)
    have middle := (first.add (hpq.mul_const v.xxy)).add (hpqq.mul_const v.xx)
    apply ((middle.add (hppqq.mul_const v.x)).add hpppqq).congr_deriv
    simp only [Pi.pow_apply]
    ring

end LengthGrowth.RecordCommutator

#print axioms LengthGrowth.RecordCommutator.commutator_coefficient
#print axioms LengthGrowth.RecordCommutator.step_derivatives
