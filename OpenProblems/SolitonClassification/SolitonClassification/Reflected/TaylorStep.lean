import SolitonClassification.Rotating.UniversalStateOrders
import SolitonClassification.Rotating.FixedTaylor

namespace SolitonClassification.Reflected
open SolitonClassification.Rotating SolitonClassification.Rotating.UniversalMajorant
open Set

def mesh : Nat := 10^28
def order : Nat := 20
def padding : Int := 10^9
abbrev Box := Vector FixedBall 6

def boxFn (b : Box) : FixedVector := fun i => b[i.val]

/-- The uniform analytic remainder and the integer polynomial enclosure both
apply to each individual real initial point of the input box. -/
def advance (h : ℚ) (b : Box) : Box :=
  (fixedTaylorEndpoint mesh h (boxFn b) order).map fun z =>
    { z with radius := z.radius + padding }

theorem scalar_budget :
    stateResidualAtCap order ≤ 6/10^18 ∧
    (19/2)*(stateScalarValueAtCap order-1) ≤ 129/250 := by
  decide +kernel

theorem advance_sound {a : State} {b : Box} (hb : ∀i, (boxFn b i).Contains mesh (a i))
    (ha : a ∈ innerTube) {h : ℚ} (hh : h ∈ Icc 0 universalStepCap) (i : Fin 6) :
    (boxFn (advance h b) i).Contains mesh (supportFlow 1 (by norm_num) (h:ℝ) a i) := by
  have ht : (h:ℝ) ∈ Icc 0 (universalStepCap:ℝ) :=
    ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩
  have herr := universal_signed_trueTaylor_order_error 1 (by norm_num) ha (N:=order)
      (ε:=6/10^18) (δ:=1/10^19) (by norm_num) (by norm_num)
      scalar_budget.1 scalar_budget.2 (by norm_num [universalStepCap]) ht
  have hcoord := (coordinate_bound _ i).trans herr
  simp only [one_mul, Pi.sub_apply, polynomialPath] at hcoord
  have hp := fixedTaylorEndpoint_contains (S:=mesh) (by norm_num [mesh]) h hb order i
  let z := (fixedTaylorEndpoint mesh h (boxFn b) order)[i.val]
  change |(taylorPolynomial a order i).eval (h:ℝ) - ((z.center:ℚ)/mesh:ℚ)| ≤
    (((z.radius:ℚ)/mesh:ℚ):ℝ) at hp
  change |supportFlow 1 _ (h:ℝ) a i - _| ≤ _
  simp only [advance, boxFn, Vector.getElem_map]
  change |supportFlow 1 _ (h:ℝ) a i - (((z.center:ℚ)/mesh:ℚ):ℝ)| ≤
    ((((z.radius+padding:ℤ):ℚ)/mesh:ℚ):ℝ)
  calc
    _ ≤ |supportFlow 1 _ (h:ℝ) a i - (taylorPolynomial a order i).eval (h:ℝ)| +
        |(taylorPolynomial a order i).eval (h:ℝ) - (((z.center:ℚ)/mesh:ℚ):ℝ)| :=
      abs_sub_le _ _ _
    _ ≤ _ := by
      have := add_le_add hcoord hp
      push_cast at this ⊢
      norm_num [mesh,padding] at this ⊢
      linarith

end SolitonClassification.Reflected
#print axioms SolitonClassification.Reflected.advance_sound
