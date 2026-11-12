import SolitonClassification.Rotating.FirstResidualIntegerBudget60
import SolitonClassification.Rotating.SignedLocalTail

/-! A concrete actual-ODE first segment, from kernel-checked finite residual
and tube data. This is not yet a many-segment orbit or shooting certificate. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Candidate FirstResidualInteger60
set_option Elab.async false

def FixedBall.widenOne (b : FixedBall) : FixedBall := ⟨b.center,b.radius+1⟩

theorem FixedBall.contains_widenOne {S : ℕ} {b : FixedBall} {x y : ℝ}
    (hy : b.Contains S y) (hxy : |x-y|≤1/(S:ℝ)) : (b.widenOne).Contains S x := by
  simp only [FixedBall.Contains,FixedBall.toRational,RationalBall.Contains,
    FixedBall.widenOne,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,Int.cast_add,Int.cast_one,
    Rat.cast_add,Rat.cast_one] at *
  calc
    _ ≤ |x-y|+|y-(b.center:ℝ)/S| := abs_sub_le _ _ _
    _ ≤ 1/(S:ℝ)+(b.radius:ℝ)/S := add_le_add hxy hy
    _ = _ := by ring

theorem first_actual_segment_error (σ : ℝ) (hσ : |σ|≤1) {t : ℝ}
    (ht : t∈Icc 0 (step:ℝ)) :
    ‖supportFlow σ hσ t initial-polynomialPath (taylorPolynomial initial 60) (σ*t)‖≤
      2*((1:ℝ)/10^80)*t := by
  have hs : (step:ℝ)≤1/125 := by
    have h : step<1/125 := step_below_cap.trans cap_below_local_time
    have h' : (step:ℝ)<((1/125:ℚ):ℝ) := Rat.cast_lt.mpr h
    norm_num at h'
    exact h'.le
  have ha (s : ℝ) (ht : s∈Icc 0 (step:ℝ)) : |σ*s|≤(budgetTime:ℝ) := by
    rw [abs_mul,abs_of_nonneg ht.1]
    calc
      _ ≤ 1*s := mul_le_mul_of_nonneg_right hσ ht.1
      _ = s := one_mul _
      _ ≤ (step:ℝ) := ht.2
      _ ≤ 1/125 := hs
      _ ≤ (budgetTime:ℝ) := by norm_num [budgetTime]
  exact signedTrueTaylorSegment_error σ hσ initial_mem_innerTube 60 hs (by positivity)
    (fun s h=>actual_polynomial_tube (ha s h)) (fun s h=>actual_residual_bound (ha s h)) t ht

theorem first_actual_segment_error_below_mesh (σ : ℝ) (hσ : |σ|≤1) {t : ℝ}
    (ht : t∈Icc 0 (step:ℝ)) :
    ‖supportFlow σ hσ t initial-polynomialPath (taylorPolynomial initial 60) (σ*t)‖≤
      1/(mesh:ℝ) := by
  apply (first_actual_segment_error σ hσ ht).trans
  have hs : (step:ℝ)≤1 := by
    have h : step<1 := step_below_cap.trans (by norm_num [stepCap])
    have hr : (step:ℝ)<((1:ℚ):ℝ) := Rat.cast_lt.mpr h
    simpa only [Rat.cast_one] using hr.le
  have h := mul_le_mul_of_nonneg_left (ht.2.trans hs) (show 0≤2*((1:ℝ)/10^80) by positivity)
  exact h.trans (by norm_num [mesh])

theorem first_true_forward_endpoint (i : Fin 6) :
    (BenchState60.endpointData[i.val].widenOne).Contains mesh
      (supportFlow 1 (by norm_num) (step:ℝ) initial i) := by
  apply FixedBall.contains_widenOne (BenchState60.endpoint_enclosed i)
  have ht : (step:ℝ)∈Icc 0 (step:ℝ) := ⟨(Rat.cast_pos.mpr positive_step).le,le_rfl⟩
  have h:=first_actual_segment_error_below_mesh 1 (by norm_num) ht
  simpa only [one_mul,polynomialPath,Pi.sub_apply] using
    (coordinate_bound (supportFlow 1 (by norm_num) (step:ℝ) initial-
      polynomialPath (taylorPolynomial initial 60) (step:ℝ)) i).trans
        (by simpa only [one_mul] using h)

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.first_true_forward_endpoint
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Concrete true first ODE segment audit passed."
