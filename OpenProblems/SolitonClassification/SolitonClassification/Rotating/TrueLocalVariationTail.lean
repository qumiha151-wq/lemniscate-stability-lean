import SolitonClassification.Rotating.TrueLocalStateTail
import SolitonClassification.Rotating.FlowVariationalODE
import SolitonClassification.Rotating.FieldHessian

/-! Actual variational-column truncation. This compares the actual initial
derivative of the chosen flow with the full-state variational polynomial.
The forcing includes the state-trajectory error; it is not merely a bound
for a matrix ODE along the approximate polynomial path. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Polynomial

theorem polynomialPath_variation_zero (a v : State) (N : ℕ) :
    polynomialPath (variationPolynomial a v N) 0=v := by
  funext i
  change (variationPolynomial a v N i).eval 0=v i
  rw [←coeff_zero_eq_eval_zero,variationPolynomial_coeff,if_pos (Nat.zero_le _),variationCoeff_zero]

theorem variation_residual_actual (a v : State) (N : ℕ) (t : ℝ) :
    polynomialPath (variationResidual a v N) t=
      polynomialVelocity (variationPolynomial a v N) t-
        fderiv ℝ field (polynomialPath (taylorPolynomial a N) t)
          (polynomialPath (variationPolynomial a v N) t) := by
  have h:=polynomialVariation_eval (taylorPolynomial a N) (variationPolynomial a v N) t
  funext i
  have hi:=congrFun h i
  change ((derivative (variationPolynomial a v N i))-
    polynomialVariation (taylorPolynomial a N) (variationPolynomial a v N) i).eval t=_
  rw [Polynomial.eval_sub,hi]
  rfl

theorem actualVariationColumn_error {T : ℝ} {c a v : State} {R E C ε : ℝ} (N : ℕ)
    (hreg : FlowTubeNeighborhood 1 (by norm_num) T c R) (ha : a∈Metric.ball c R)
    (hT : T≤1/125) (hE : 0≤E) (hC : 0≤C) (hε : 0≤ε)
    (hp : ∀t∈Icc 0 T,polynomialPath (taylorPolynomial a N) t∈outerTube)
    (hstate : ∀t∈Icc 0 T,
      ‖supportFlow 1 (by norm_num) t a-polynomialPath (taylorPolynomial a N) t‖≤E)
    (hw : ∀t∈Icc 0 T,‖polynomialPath (variationPolynomial a v N) t‖≤C)
    (hr : ∀t∈Icc 0 T,‖polynomialPath (variationResidual a v N) t‖≤ε) :
    ∀t∈Icc 0 T,
      ‖fderiv ℝ (supportFlow 1 (by norm_num) t) a v-polynomialPath (variationPolynomial a v N) t‖≤
        2*(4*E*C+ε)*t := by
  let x : ℝ → State := fun t=>supportFlow 1 (by norm_num) t a
  let y : ℝ → State := fun t=>fderiv ℝ (supportFlow 1 (by norm_num) t) a v
  let p : ℝ → State := polynomialPath (taylorPolynomial a N)
  let w : ℝ → State := polynomialPath (variationPolynomial a v N)
  let w' : ℝ → State := polynomialVelocity (variationPolynomial a v N)
  let z : ℝ → State := polynomialPath (variationResidual a v N)
  have hy : ContinuousOn y (Icc 0 T) :=
    (supportFlow_fderiv_time_continuousOn 1 (by norm_num) hreg ha).clm_apply continuousOn_const
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun t=>
    (polynomialPath_hasDerivAt _ t).continuousAt
  have hyd : ∀t∈Ico 0 T,HasDerivWithinAt y (fderiv ℝ field (x t) (y t)) (Ici t) t := by
    intro t ht
    have h:=(supportFlow_fderiv_hasDerivWithinAt 1 (by norm_num) hreg ha ht).clm_apply
      (hasDerivWithinAt_const t (Ici t) v)
    simpa [y,x,flowLinearCoefficient,ContinuousLinearMap.comp_apply] using h
  have hd : ∀t∈Ico 0 T,HasDerivWithinAt (fun t=>y t-w t)
      (fderiv ℝ field (x t) (y t)-w' t) (Ici t) t := by
    intro t ht
    exact (hyd t ht).sub (polynomialPath_hasDerivAt _ t).hasDerivWithinAt
  have hinit : ‖y 0-w 0‖≤0 := by
    simp [y,w,supportFlow_fderiv_initial,polynomialPath_variation_zero]
  have hb : ∀t∈Ico 0 T,‖fderiv ℝ field (x t) (y t)-w' t‖≤17*‖y t-w t‖+(4*E*C+ε) := by
    intro t ht
    have ht' : t∈Icc 0 T := Ico_subset_Icc_self ht
    have hx : x t∈outerTube := hreg a ha t ht'
    have he : fderiv ℝ field (x t) (y t)-w' t=
        fderiv ℝ field (x t) (y t-w t)+
          (fderiv ℝ field (x t)-fderiv ℝ field (p t)) (w t)-z t := by
      dsimp only [z,w',p,w]
      rw [variation_residual_actual]
      simp only [map_sub,ContinuousLinearMap.sub_apply]
      abel
    have hlin : ‖fderiv ℝ field (x t) (y t-w t)‖≤17*‖y t-w t‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (field_fderiv_bound hx) (norm_nonneg _))
    have hdiff : ‖fderiv ℝ field (x t)-fderiv ℝ field (p t)‖≤4*E :=
      (field_fderiv_difference hx (hp t ht')).trans (mul_le_mul_of_nonneg_left (hstate t ht') (by norm_num))
    have hforcing : ‖(fderiv ℝ field (x t)-fderiv ℝ field (p t)) (w t)‖≤4*E*C :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hdiff (hw t ht') (norm_nonneg _) (by positivity))
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hlin hforcing)) (hr t ht')) |>.trans (by ring_nf; rfl)
  have he:=norm_le_gronwallBound_of_norm_deriv_right_le (hy.sub hwc.continuousOn) hd hinit hb
  intro t ht
  have hnonneg : 0≤4*E*C+ε := by positivity
  have he':=he t ht
  simp only [sub_zero] at he'
  exact he'.trans (short_gronwall_bound hnonneg ht.1 (ht.2.trans hT))

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.actualVariationColumn_error
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Actual-flow variational-column truncation audit passed."
