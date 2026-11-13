module

public import SolitonClassification.Rotating.ResidualODE

@[expose] public section

/-! Actual second Frechet derivatives of the polynomial support field.
The bound four is proved for the genuine derivative, not a formal polynomial
coefficient or an external interval report. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem field_fderiv_differentiable : Differentiable ℝ (fderiv ℝ field) :=
  ((field_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).fderiv_right
    (m:=1) (by norm_num)).differentiable (by norm_num)

theorem linear_line_expansion (a u v : State) (t : ℝ) :
    linear (a+t • u) v=linear a v+t • (bilinear a u v+bilinear a v u)+
      t^2 • ((3:ℝ) • trilinear u u v) := by
  ext i
  fin_cases i <;> simp [linear,bilinear,trilinear,smul_eq_mul] <;> ring

theorem field_second_fderiv_apply (a u v : State) :
    fderiv ℝ (fderiv ℝ field) a u v=bilinear a u v+bilinear a v u := by
  have hp : HasDerivAt (fun t : ℝ => a+t • u) u 0 := by
    convert! (hasDerivAt_const (0:ℝ) a).add ((hasDerivAt_id (0:ℝ)).smul_const u) using 1
    simp
  have hD := ((field_fderiv_differentiable a).hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)).clm_apply
    (hasDerivAt_const (0:ℝ) v)
  have hpoly := ((hasDerivAt_const (0:ℝ) (linear a v)).add
    ((hasDerivAt_id (0:ℝ)).smul_const (bilinear a u v+bilinear a v u))).add
      (((hasDerivAt_id (0:ℝ)).pow 2).smul_const ((3:ℝ) • trilinear u u v))
  have hline : HasDerivAt (fun t : ℝ => fderiv ℝ field (a+t • u) v)
      (bilinear a u v+bilinear a v u) 0 := by
    convert! hpoly using 1
    · funext t
      rw [field_fderiv_apply,linear_line_expansion]
      rfl
    · simp
  simpa only [map_zero,add_zero] using hD.unique hline

theorem field_second_fderiv_bound {a : State} (ha : a∈outerTube) :
    ‖fderiv ℝ (fderiv ℝ field) a‖≤4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [field_second_fderiv_apply]
  have h1 := bilinear_bound ha u v
  have h2 := bilinear_bound ha v u
  have hn := norm_add_le (bilinear a u v) (bilinear a v u)
  nlinarith

theorem field_fderiv_lipschitz_on : LipschitzOnWith 4 (fderiv ℝ field) outerTube := by
  apply outerTube_convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜:=ℝ)
  · intro a _
    exact field_fderiv_differentiable a
  · intro a ha
    exact field_second_fderiv_bound ha

theorem field_fderiv_difference {a b : State} (ha : a∈outerTube) (hb : b∈outerTube) :
    ‖fderiv ℝ field a-fderiv ℝ field b‖≤4*‖a-b‖ := by
  simpa only [dist_eq_norm,NNReal.coe_ofNat] using field_fderiv_lipschitz_on.dist_le_mul a ha b hb

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual field Hessian audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual field Hessian audit passed for {count} declarations."

end
