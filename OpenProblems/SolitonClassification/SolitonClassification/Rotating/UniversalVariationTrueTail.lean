import SolitonClassification.Rotating.UniversalVariationTrueTailNeighborhood
import SolitonClassification.Rotating.UniversalVariationMajorantBudget
import SolitonClassification.Rotating.UniversalTrueStateTail

/-! Actual signed variational tails with mixed state and variation orders.
The generic comparison independently adapts SignedLocalTail's proved
same-order argument, retaining the actual state-error forcing4EC+epsilon.
The final order60/30 theorem supplies every tube, state-error and residual
hypothesis and applies even to initial points on the innerTube boundary. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Set Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem signedActualMixedVariationColumn_error (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c a v : State} {R E C ε : ℝ} (M N : ℕ)
    (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hT : T≤1/125) (hE : 0≤E) (hC : 0≤C) (hε : 0≤ε)
    (hp : ∀t∈Icc 0 T,polynomialPath (taylorPolynomial a M) (σ*t)∈outerTube)
    (hstate : ∀t∈Icc 0 T,
      ‖supportFlow σ hσ t a-polynomialPath (taylorPolynomial a M) (σ*t)‖≤E)
    (hw : ∀t∈Icc 0 T,‖polynomialPath (variationPolynomial a v N) (σ*t)‖≤C)
    (hr : ∀t∈Icc 0 T,‖polynomialPath (mixedVariationResidual a v M N) (σ*t)‖≤ε) :
    ∀t∈Icc 0 T,
      ‖fderiv ℝ (supportFlow σ hσ t) a v-polynomialPath (variationPolynomial a v N) (σ*t)‖≤
        2*(4*E*C+ε)*t := by
  let x : ℝ → State := fun t => supportFlow σ hσ t a
  let y : ℝ → State := fun t => fderiv ℝ (supportFlow σ hσ t) a v
  let p : ℝ → State := fun t => polynomialPath (taylorPolynomial a M) (σ*t)
  let w : ℝ → State := fun t => polynomialPath (variationPolynomial a v N) (σ*t)
  let w' : ℝ → State := fun t => polynomialVelocity (variationPolynomial a v N) (σ*t)
  let z : ℝ → State := fun t => polynomialPath (mixedVariationResidual a v M N) (σ*t)
  have hy : ContinuousOn y (Icc 0 T) :=
    (supportFlow_fderiv_time_continuousOn σ hσ hreg ha).clm_apply continuousOn_const
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun t =>
    (signedPolynomial_hasDerivAt σ _ t).continuousAt
  have hyd : ∀t∈Ico 0 T,HasDerivWithinAt y (σ • fderiv ℝ field (x t) (y t)) (Ici t) t := by
    intro t ht
    have h := (supportFlow_fderiv_hasDerivWithinAt σ hσ hreg ha ht).clm_apply
      (hasDerivWithinAt_const t (Ici t) v)
    simpa [y,x,flowLinearCoefficient,ContinuousLinearMap.comp_apply] using h
  have hd : ∀t∈Ico 0 T,HasDerivWithinAt (fun t => y t-w t)
      (σ • fderiv ℝ field (x t) (y t)-σ • w' t) (Ici t) t := by
    intro t ht
    exact (hyd t ht).sub (signedPolynomial_hasDerivAt σ _ t).hasDerivWithinAt
  have hinit : ‖y 0-w 0‖≤0 := by
    simp [y,w,supportFlow_fderiv_initial,polynomialPath_variation_zero]
  have hb : ∀t∈Ico 0 T,‖σ • fderiv ℝ field (x t) (y t)-σ • w' t‖≤
      17*‖y t-w t‖+(4*E*C+ε) := by
    intro t ht
    have ht' : t∈Icc 0 T := Ico_subset_Icc_self ht
    have hx : x t∈outerTube := hreg a ha t ht'
    have he : fderiv ℝ field (x t) (y t)-w' t=
        fderiv ℝ field (x t) (y t-w t)+
          (fderiv ℝ field (x t)-fderiv ℝ field (p t)) (w t)-z t := by
      dsimp only [z,w',p,w]
      rw [mixedVariationResidual_actual]
      simp only [map_sub,sub_apply]
      abel
    have hlin : ‖fderiv ℝ field (x t) (y t-w t)‖≤17*‖y t-w t‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (field_fderiv_bound hx) (norm_nonneg _))
    have hdiff : ‖fderiv ℝ field (x t)-fderiv ℝ field (p t)‖≤4*E :=
      (field_fderiv_difference hx (hp t ht')).trans
        (mul_le_mul_of_nonneg_left (hstate t ht') (by norm_num))
    have hforcing : ‖(fderiv ℝ field (x t)-fderiv ℝ field (p t)) (w t)‖≤4*E*C :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hdiff (hw t ht') (norm_nonneg _) (by positivity))
    rw [←smul_sub]
    apply (norm_smul_le_of_abs_le_one σ hσ _).trans
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hlin hforcing)) (hr t ht')) |>.trans (by ring_nf; rfl)
  have he := norm_le_gronwallBound_of_norm_deriv_right_le (hy.sub hwc.continuousOn) hd hinit hb
  intro t ht
  have hnonneg : 0≤4*E*C+ε := by positivity
  have he' := he t ht
  simp only [sub_zero] at he'
  exact he'.trans (short_gronwall_bound hnonneg ht.1 (ht.2.trans hT))

/-- Actual initial-data derivative error, for every innerTube initial point,
including its boundary. No assumed flow tube, numerical residual, or state
error remains in this theorem's hypotheses. -/
theorem universal_signed_trueVariation60_30_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) (v : State) {t : ℝ}
    (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖fderiv ℝ (supportFlow σ hσ t) a v-
      polynomialPath (variationPolynomial a v 30) (σ*t)‖≤‖v‖*((7:ℝ)/10^29) := by
  have hreg : FlowTubeNeighborhood σ hσ (universalStepCap:ℝ) a (1/10000) :=
    innerTube_flowTubeNeighborhood σ hσ ha universalStepCap_le_local
  have haball : a∈Metric.ball a (1/10000:ℝ) := Metric.mem_ball_self (by norm_num)
  have hs (s : ℝ) (hs : s∈Icc 0 (universalStepCap:ℝ)) : |σ*s|≤(universalStepCap:ℝ) := by
    rw [abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_right hσ hs.1).trans (by simpa using hs.2)
  have h := signedActualMixedVariationColumn_error σ hσ 60 30 hreg haball
    (E:=(2:ℝ)/10^59) (C:=‖v‖*(6/5)) (ε:=‖v‖*(4/10^27))
    universalStepCap_le_local (by positivity) (by positivity) (by positivity)
    (fun s h => taylorPolynomial60_tube_uniform ha (hs s h))
    (fun s h => universal_signed_trueTaylor60_error_uniform σ hσ ha h)
    (fun s h => variationPolynomial30_uniform ha v (hs s h))
    (fun s h => mixedVariationResidual60_30_uniform ha v (hs s h)) t ht
  apply h.trans
  calc
    _ = ‖v‖*(2*(4*((2:ℝ)/10^59)*(6/5)+4/10^27)*t) := by ring
    _ ≤ ‖v‖*(2*(4*((2:ℝ)/10^59)*(6/5)+4/10^27)*(universalStepCap:ℝ)) := by
      gcongr
      exact ht.2
    _ ≤ _ := mul_le_mul_of_nonneg_left (by norm_num [universalStepCap]) (norm_nonneg v)

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.universal_signed_trueVariation60_30_error
open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Universal actual mixed-order variational tail audit passed; standard axioms only."
