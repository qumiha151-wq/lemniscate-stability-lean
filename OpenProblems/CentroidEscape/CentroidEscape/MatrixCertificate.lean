import CentroidEscape.ShootingRootMatrixBridge

/-!
# Executable rational checks for the shooting preconditioner

All checks operate on finite rational data. Their soundness is proved for
the actual real continuous linear operators used by the root theorem.
-/
namespace CentroidEscape
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

abbrev RationalVector3 := Fin 3 → ℚ
abbrev RationalMatrix3 := Fin 3 → Fin 3 → ℚ

def castRationalVector3 (v : RationalVector3) : Fin 3 → ℝ := fun i=>(v i:ℝ)

def rationalMatrixOperator (M : RationalMatrix3) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  columnOperator (fun j i=>(M i j:ℝ))

lemma rationalMatrixOperator_apply (M : RationalMatrix3) (v : Fin 3 → ℝ) (i : Fin 3) :
    rationalMatrixOperator M v i=∑ j : Fin 3, (M i j:ℝ)*v j := by
  simp [rationalMatrixOperator,columnOperator_apply,Finset.sum_apply,mul_comm]

def rationalMatrixProduct (A B : RationalMatrix3) : RationalMatrix3 :=
  fun i j=>∑ k : Fin 3, A i k*B k j

def rationalIdentity3 : RationalMatrix3 := fun i j=>if i=j then 1 else 0

def rationalMatrixVector (A : RationalMatrix3) (v : RationalVector3) : RationalVector3 :=
  fun i=>∑ j : Fin 3, A i j*v j

lemma rationalMatrixOperator_product (A B : RationalMatrix3) :
    rationalMatrixOperator (rationalMatrixProduct A B)=
      (rationalMatrixOperator A).comp (rationalMatrixOperator B) := by
  ext v i
  simp only [ContinuousLinearMap.comp_apply,rationalMatrixOperator_apply,
    rationalMatrixProduct,Fin.sum_univ_succ,Rat.cast_add,Rat.cast_mul]
  ring

lemma rationalMatrixOperator_sub (A B : RationalMatrix3) :
    rationalMatrixOperator (A-B)=rationalMatrixOperator A-rationalMatrixOperator B := by
  ext v i
  simp only [sub_apply,Pi.sub_apply,rationalMatrixOperator_apply,
    Fin.sum_univ_succ,Rat.cast_sub]
  ring

lemma rationalMatrixOperator_identity :
    rationalMatrixOperator rationalIdentity3=ContinuousLinearMap.id ℝ (Fin 3 → ℝ) := by
  ext v i
  fin_cases i <;> simp [rationalMatrixOperator_apply,rationalIdentity3,Fin.sum_univ_succ]

lemma rationalMatrixOperator_vector (A : RationalMatrix3) (v : RationalVector3) :
    rationalMatrixOperator A (castRationalVector3 v)=castRationalVector3 (rationalMatrixVector A v) := by
  ext i
  simp [rationalMatrixOperator_apply,castRationalVector3,rationalMatrixVector,
    Fin.sum_univ_succ]

def checkRationalMatrixBound (M : RationalMatrix3) (β : ℚ) : Bool :=
  decide (0≤β ∧ ∀ i, (∑ j : Fin 3, |M i j|)≤β)

def checkRationalVectorBound (v : RationalVector3) (η : ℚ) : Bool :=
  decide (0≤η ∧ ∀ i, |v i|≤η)

theorem checkRationalMatrixBound_sound {M : RationalMatrix3} {β : ℚ}
    (hcheck : checkRationalMatrixBound M β=true) : ‖rationalMatrixOperator M‖≤(β:ℝ) := by
  have h : 0≤β ∧ ∀i, (∑ j : Fin 3, |M i j|)≤β := of_decide_eq_true hcheck
  have hβ : (0:ℝ)≤(β:ℝ) := Rat.cast_nonneg.mpr h.1
  apply ContinuousLinearMap.opNorm_le_bound _ hβ
  intro v
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ (norm_nonneg v))]
  intro i
  have hrow : (∑ j : Fin 3, ‖(M i j:ℝ)‖)≤(β:ℝ) := by
    have hh := h.2 i
    have hc : (∑ j : Fin 3, |(M i j:ℝ)|)≤(β:ℝ) := by exact_mod_cast hh
    simpa only [Real.norm_eq_abs] using hc
  rw [rationalMatrixOperator_apply]
  calc
    ‖∑ j : Fin 3, (M i j:ℝ)*v j‖ ≤∑ j : Fin 3, ‖(M i j:ℝ)*v j‖ := norm_sum_le _ _
    _ ≤∑ j : Fin 3, ‖(M i j:ℝ)‖*‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
    _ = (∑ j : Fin 3, ‖(M i j:ℝ)‖)*‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤(β:ℝ)*‖v‖ := mul_le_mul_of_nonneg_right hrow (norm_nonneg v)

theorem checkRationalVectorBound_sound {v : RationalVector3} {η : ℚ}
    (hcheck : checkRationalVectorBound v η=true) : ‖castRationalVector3 v‖≤(η:ℝ) := by
  have h : 0≤η ∧ ∀i, |v i|≤η := of_decide_eq_true hcheck
  rw [pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr h.1)]
  intro i
  change ‖(v i:ℝ)‖≤(η:ℝ)
  rw [Real.norm_eq_abs]
  exact_mod_cast h.2 i

theorem rational_preconditioner_checks {B J : RationalMatrix3} {y : RationalVector3}
    {β q₀ ζ : ℚ}
    (hB : checkRationalMatrixBound B β=true)
    (hJ : checkRationalMatrixBound (rationalIdentity3-rationalMatrixProduct B J) q₀=true)
    (hy : checkRationalVectorBound (rationalMatrixVector B y) ζ=true) :
    ‖rationalMatrixOperator B‖≤(β:ℝ) ∧
    ‖ContinuousLinearMap.id ℝ (Fin 3 → ℝ)-
      (rationalMatrixOperator B).comp (rationalMatrixOperator J)‖≤(q₀:ℝ) ∧
    ‖rationalMatrixOperator B (castRationalVector3 y)‖≤(ζ:ℝ) := by
  refine ⟨checkRationalMatrixBound_sound hB,?_,?_⟩
  · have hh := checkRationalMatrixBound_sound hJ
    simpa only [rationalMatrixOperator_sub,rationalMatrixOperator_identity,rationalMatrixOperator_product] using hh
  · rw [rationalMatrixOperator_vector]
    exact checkRationalVectorBound_sound hy

end
end CentroidEscape

#print axioms CentroidEscape.rational_preconditioner_checks

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Rational matrix certificate audit passed for {checked} declarations."
