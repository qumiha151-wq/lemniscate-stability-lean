module

public import SolitonClassification.Rotating.QuantitativeVariation

@[expose] public section

/-! Sharp joint derivative variation from actual fundamental/inverse bounds.
All constants concern the actual ODE flow already constructed in this project. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem supportFlow_fderiv_time_variation_sharp (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R K : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R)
    (hPbound : ∀r∈Icc 0 T,‖fderiv ℝ (supportFlow σ hσ r) a‖≤K)
    {s t : ℝ} (hs : s∈Icc 0 T) (ht : t∈Icc 0 T) :
    ‖fderiv ℝ (supportFlow σ hσ t) a-fderiv ℝ (supportFlow σ hσ s) a‖≤17*K*dist t s := by
  let P : ℝ → State →L[ℝ] State := fun r => fderiv ℝ (supportFlow σ hσ r) a
  have H {s t : ℝ} (hs : s∈Icc 0 T) (ht : t∈Icc 0 T) (hst : s≤t) :
      ‖P t-P s‖≤17*K*dist t s := by
    have hsub : Icc s t⊆Icc 0 T := Icc_subset_Icc hs.1 ht.2
    have hc := (supportFlow_fderiv_time_continuousOn σ hσ hreg ha).mono hsub
    have hd : ∀r∈Ico s t,HasDerivWithinAt (fun u => P u-P s)
        ((flowLinearCoefficient σ hσ a r).comp (P r)) (Ici r) r := by
      intro r hr
      exact (supportFlow_fderiv_hasDerivWithinAt σ hσ hreg ha
        ⟨hs.1.trans hr.1,hr.2.trans_le ht.2⟩).sub_const (P s)
    have hbound : ∀r∈Ico s t,‖(flowLinearCoefficient σ hσ a r).comp (P r)‖≤17*K := by
      intro r hr
      have hr' := hsub (Ico_subset_Icc_self hr)
      exact ((flowLinearCoefficient σ hσ a r).opNorm_comp_le _).trans
        (mul_le_mul (flowLinearCoefficient_bound σ hσ (hreg a ha r hr'))
          (hPbound r hr') (norm_nonneg _) (by norm_num))
    have hn := norm_le_gronwallBound_of_norm_deriv_right_le
      (f:=fun r => P r-P s) (f':=fun r => (flowLinearCoefficient σ hσ a r).comp (P r))
      (δ:=0) (K:=0) (ε:=17*K) (hc.sub continuousOn_const) hd (by simp)
      (fun r hr => by simpa only [zero_mul,zero_add] using hbound r hr) t ⟨hst,le_rfl⟩
    simpa only [gronwallBound_K0,zero_add,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hst)] using hn
  rcases le_total s t with hst|hts
  · exact H hs ht hst
  · simpa only [norm_sub_rev,dist_comm] using H ht hs hts

def trueJointVariationBudget (T K I : ℝ) : ℝ := 4*K^3*I*T+34*K+1275

theorem supportFlowDifferential_sharp_variation (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} (hT : 0≤T) {c : State} {R K I : ℝ} {S : Set State}
    (hK : 0≤K) (hI : 0≤I) (hreg : FlowTubeNeighborhood σ hσ T c R)
    (hS : Convex ℝ S) (hsub : S⊆Metric.ball c R)
    (hPbound : ∀a∈S,∀t∈Icc 0 T,‖fderiv ℝ (supportFlow σ hσ t) a‖≤K)
    (Q : State → ℝ → State →L[ℝ] State)
    (hQc : ∀a∈S,ContinuousOn (Q a) (Icc 0 T))
    (hPQ : ∀a∈S,∀t∈Icc 0 T,
      (fderiv ℝ (supportFlow σ hσ t) a).comp (Q a t)=ContinuousLinearMap.id ℝ State)
    (hQbound : ∀a∈S,∀t∈Icc 0 T,‖Q a t‖≤I)
    {p q : ℝ×State} (hp : p∈Icc 0 T ×ˢ S) (hq : q∈Icc 0 T ×ˢ S) :
    ‖supportFlowDifferential σ hσ p-supportFlowDifferential σ hσ q‖≤
      trueJointVariationBudget T K I*dist p q := by
  have h1 : dist p.1 q.1≤dist p q := le_max_left _ _
  have h2 : dist p.2 q.2≤dist p q := le_max_right _ _
  have hstate : ‖supportFlow σ hσ p.1 p.2-supportFlow σ hσ q.1 q.2‖≤(K+75)*dist p q := by
    have hs := supportFlow_distance_of_true_derivative_bound σ hσ hreg hS hsub hPbound hq.2 hp.2 hp.1
    have ht := (supportFlow_time_lipschitz σ hσ q.2).dist_le_mul p.1 q.1
    have htri := norm_sub_le_norm_sub_add_norm_sub (supportFlow σ hσ p.1 p.2)
      (supportFlow σ hσ p.1 q.2) (supportFlow σ hσ q.1 q.2)
    have hm := mul_le_mul_of_nonneg_left h2 hK
    simp only [dist_eq_norm,NNReal.coe_ofNat] at ht
    rw [Real.norm_eq_abs] at ht
    rw [dist_eq_norm p.2 q.2] at hm
    rw [Real.dist_eq] at h1
    nlinarith
  have hP : ‖fderiv ℝ (supportFlow σ hσ p.1) p.2-fderiv ℝ (supportFlow σ hσ q.1) q.2‖≤
      (4*K^3*I*T+17*K)*dist p q := by
    have hs := supportFlow_fderiv_sharp_variation σ hσ hT hK hI hreg hS hsub hPbound
      hq.2 hp.2 (Q q.2) (hQc q.2 hq.2) (hPQ q.2 hq.2) (hQbound q.2 hq.2) p.1 hp.1
    have ht := supportFlow_fderiv_time_variation_sharp σ hσ hreg (hsub hq.2) (hPbound q.2 hq.2) hq.1 hp.1
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (fderiv ℝ (supportFlow σ hσ p.1) p.2) (fderiv ℝ (supportFlow σ hσ p.1) q.2)
      (fderiv ℝ (supportFlow σ hσ q.1) q.2)
    have hsT : 4*K^3*I*p.1*‖p.2-q.2‖≤4*K^3*I*T*‖p.2-q.2‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp.1.2 (by positivity)) (norm_nonneg _)
    have hm1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0≤17*K)
    have hm2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0≤4*K^3*I*T)
    rw [dist_eq_norm p.2 q.2] at hm2
    nlinarith
  have hg : ‖signedClippedField σ (supportFlow σ hσ p.1 p.2)-
      signedClippedField σ (supportFlow σ hσ q.1 q.2)‖≤17*(K+75)*dist p q := by
    have h := (signedClippedField_lipschitz hσ).dist_le_mul
      (supportFlow σ hσ p.1 p.2) (supportFlow σ hσ q.1 q.2)
    simp only [dist_eq_norm,NNReal.coe_ofNat] at h
    nlinarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold trueJointVariationBudget; positivity)
  intro v
  let gp := signedClippedField σ (supportFlow σ hσ p.1 p.2)
  let gq := signedClippedField σ (supportFlow σ hσ q.1 q.2)
  let Pp := fderiv ℝ (supportFlow σ hσ p.1) p.2
  let Pq := fderiv ℝ (supportFlow σ hσ q.1) q.2
  have he : (supportFlowDifferential σ hσ p-supportFlowDifferential σ hσ q) v=
      v.1 • (gp-gq)+(Pp-Pq) v.2 := by
    simp only [supportFlowDifferential,ContinuousLinearMap.coprod_apply,sub_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    dsimp [gp,gq,Pp,Pq]
    module
  have hv1 : ‖v.1‖≤‖v‖ := le_max_left _ _
  have hv2 : ‖v.2‖≤‖v‖ := le_max_right _ _
  have hg' : ‖v.1 • (gp-gq)‖≤(17*(K+75)*dist p q)*‖v‖ := by
    rw [norm_smul]
    exact (mul_le_mul hv1 hg (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hP' : ‖(Pp-Pq) v.2‖≤((4*K^3*I*T+17*K)*dist p q)*‖v‖ :=
    ((Pp-Pq).le_opNorm _).trans (mul_le_mul hP hv2 (norm_nonneg _) (by positivity))
  rw [he]
  have hn := norm_add_le (v.1 • (gp-gq)) ((Pp-Pq) v.2)
  unfold trueJointVariationBudget
  nlinarith

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating sharp joint variation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating sharp joint variation audit passed for {count} declarations."
