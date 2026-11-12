import SolitonClassification.Rotating.TrueLocalVariationTail

/-! Signed local residual comparison. The same canonical Taylor coefficients
are evaluated at σ*t, covering both halves without changing any frozen data.
Every residual is multiplied by σ; |σ|≤1 controls its norm. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Polynomial
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem norm_smul_le_of_abs_le_one (σ : ℝ) (hσ : |σ|≤1) (v : State) :
    ‖σ • v‖≤‖v‖ := by
  rw [norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg v)).trans_eq (one_mul _)

theorem signedPolynomial_hasDerivAt (σ : ℝ) (P : StatePolynomial) (t : ℝ) :
    HasDerivAt (fun s=>polynomialPath P (σ*s)) (σ • polynomialVelocity P (σ*t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  convert! ((P i).hasDerivAt (σ*t)).comp t ((hasDerivAt_id t).const_mul σ) using 1
  simp [polynomialVelocity,smul_eq_mul,mul_comm]

theorem signedTrueTaylorSegment_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) (N : ℕ)
    {T ε : ℝ} (hT : T≤1/125) (hε : 0≤ε)
    (hp : ∀t∈Icc 0 T,polynomialPath (taylorPolynomial a N) (σ*t)∈outerTube)
    (hr : ∀t∈Icc 0 T,‖polynomialPath (taylorResidual a N) (σ*t)‖≤ε) :
    ∀t∈Icc 0 T,‖supportFlow σ hσ t a-polynomialPath (taylorPolynomial a N) (σ*t)‖≤2*ε*t := by
  let x : ℝ → State := fun t=>supportFlow σ hσ t a
  let p : ℝ → State := fun t=>polynomialPath (taylorPolynomial a N) (σ*t)
  let v : ℝ → State := fun t=>polynomialVelocity (taylorPolynomial a N) (σ*t)
  let z : ℝ → State := fun t=>polynomialPath (taylorResidual a N) (σ*t)
  have hc : Continuous x := continuous_iff_continuousAt.mpr fun t=>
    (supportFlow_derivative σ hσ a t).continuousAt
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun t=>
    (signedPolynomial_hasDerivAt σ _ t).continuousAt
  have hd : ∀t∈Ico 0 T,HasDerivWithinAt (fun s=>x s-p s)
      (σ • field (x t)-σ • v t) (Ici t) t := by
    intro t ht
    exact (supportFlow_short_original σ hσ ha ht.1 (ht.2.le.trans hT)).hasDerivWithinAt.sub
      (signedPolynomial_hasDerivAt σ _ t).hasDerivWithinAt
  have hinit : ‖x 0-p 0‖≤0 := by simp [x,p,supportFlow_zero,polynomialPath_taylor_zero]
  have hb : ∀t∈Ico 0 T,‖σ • field (x t)-σ • v t‖≤17*‖x t-p t‖+ε := by
    intro t ht
    have hx : x t∈outerTube := supportFlow_short_mem_outerTube σ hσ ha ht.1 (ht.2.le.trans hT)
    have ht' : t∈Icc 0 T := Ico_subset_Icc_self ht
    have hf : ‖field (x t)-field (p t)‖≤17*‖x t-p t‖ :=
      lipschitzOnWith_iff_norm_sub_le.mp field_lipschitz_on hx (hp t ht')
    have he : field (x t)-v t=field (x t)-field (p t)-z t := by
      dsimp only [v,p,z]
      rw [polynomial_residual_actual]
      abel
    rw [←smul_sub]
    apply (norm_smul_le_of_abs_le_one σ hσ _).trans
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hf (hr t ht'))
  have he:=norm_le_gronwallBound_of_norm_deriv_right_le (hc.sub hpc).continuousOn hd hinit hb
  intro t ht
  have he':=he t ht
  simp only [sub_zero] at he'
  exact he'.trans (short_gronwall_bound hε ht.1 (ht.2.trans hT))

theorem signedActualVariationColumn_error (σ : ℝ) (hσ : |σ|≤1) {T : ℝ} {c a v : State} {R E C ε : ℝ} (N : ℕ)
    (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hT : T≤1/125) (hE : 0≤E) (hC : 0≤C) (hε : 0≤ε)
    (hp : ∀t∈Icc 0 T,polynomialPath (taylorPolynomial a N) (σ*t)∈outerTube)
    (hstate : ∀t∈Icc 0 T,
      ‖supportFlow σ hσ t a-polynomialPath (taylorPolynomial a N) (σ*t)‖≤E)
    (hw : ∀t∈Icc 0 T,‖polynomialPath (variationPolynomial a v N) (σ*t)‖≤C)
    (hr : ∀t∈Icc 0 T,‖polynomialPath (variationResidual a v N) (σ*t)‖≤ε) :
    ∀t∈Icc 0 T,
      ‖fderiv ℝ (supportFlow σ hσ t) a v-polynomialPath (variationPolynomial a v N) (σ*t)‖≤
        2*(4*E*C+ε)*t := by
  let x : ℝ → State := fun t=>supportFlow σ hσ t a
  let y : ℝ → State := fun t=>fderiv ℝ (supportFlow σ hσ t) a v
  let p : ℝ → State := fun t=>polynomialPath (taylorPolynomial a N) (σ*t)
  let w : ℝ → State := fun t=>polynomialPath (variationPolynomial a v N) (σ*t)
  let w' : ℝ → State := fun t=>polynomialVelocity (variationPolynomial a v N) (σ*t)
  let z : ℝ → State := fun t=>polynomialPath (variationResidual a v N) (σ*t)
  have hy : ContinuousOn y (Icc 0 T) :=
    (supportFlow_fderiv_time_continuousOn σ hσ hreg ha).clm_apply continuousOn_const
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun t=>
    (signedPolynomial_hasDerivAt σ _ t).continuousAt
  have hyd : ∀t∈Ico 0 T,HasDerivWithinAt y (σ • fderiv ℝ field (x t) (y t)) (Ici t) t := by
    intro t ht
    have h:=(supportFlow_fderiv_hasDerivWithinAt σ hσ hreg ha ht).clm_apply
      (hasDerivWithinAt_const t (Ici t) v)
    simpa [y,x,flowLinearCoefficient,ContinuousLinearMap.comp_apply] using h
  have hd : ∀t∈Ico 0 T,HasDerivWithinAt (fun t=>y t-w t)
      (σ • fderiv ℝ field (x t) (y t)-σ • w' t) (Ici t) t := by
    intro t ht
    exact (hyd t ht).sub (signedPolynomial_hasDerivAt σ _ t).hasDerivWithinAt
  have hinit : ‖y 0-w 0‖≤0 := by
    simp [y,w,supportFlow_fderiv_initial,polynomialPath_variation_zero]
  have hb : ∀t∈Ico 0 T,‖σ • fderiv ℝ field (x t) (y t)-σ • w' t‖≤17*‖y t-w t‖+(4*E*C+ε) := by
    intro t ht
    have ht' : t∈Icc 0 T := Ico_subset_Icc_self ht
    have hx : x t∈outerTube := hreg a ha t ht'
    have he : fderiv ℝ field (x t) (y t)-w' t=
        fderiv ℝ field (x t) (y t-w t)+
          (fderiv ℝ field (x t)-fderiv ℝ field (p t)) (w t)-z t := by
      dsimp only [z,w',p,w]
      rw [variation_residual_actual]
      simp only [map_sub,sub_apply]
      abel
    have hlin : ‖fderiv ℝ field (x t) (y t-w t)‖≤17*‖y t-w t‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (field_fderiv_bound hx) (norm_nonneg _))
    have hdiff : ‖fderiv ℝ field (x t)-fderiv ℝ field (p t)‖≤4*E :=
      (field_fderiv_difference hx (hp t ht')).trans (mul_le_mul_of_nonneg_left (hstate t ht') (by norm_num))
    have hforcing : ‖(fderiv ℝ field (x t)-fderiv ℝ field (p t)) (w t)‖≤4*E*C :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hdiff (hw t ht') (norm_nonneg _) (by positivity))
    rw [←smul_sub]
    apply (norm_smul_le_of_abs_le_one σ hσ _).trans
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

#print axioms SolitonClassification.Rotating.signedTrueTaylorSegment_error
#print axioms SolitonClassification.Rotating.signedActualVariationColumn_error
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Signed actual state and variation tail audit passed."
