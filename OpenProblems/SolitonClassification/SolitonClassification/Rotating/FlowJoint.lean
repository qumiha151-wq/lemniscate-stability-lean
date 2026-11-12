import SolitonClassification.Rotating.FlowDifferentiability
import SolitonClassification.Rotating.PartialDerivatives

/-! Actual joint strict derivative of the selected signed flow. The spatial
derivative was constructed from actual ODE midpoint differences. Here its
time continuity and the continuous partial derivatives give the joint result.
No smoothness of the clipped field at the clipping boundary is asserted. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Real Filter
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

theorem supportFlow_increment_lipschitz (σ : ℝ) (hσ : |σ|≤1) (T : ℝ)
    {s t : ℝ} (hs : s∈Icc 0 T) (ht : t∈Icc 0 T) :
    LipschitzWith ⟨17*exp (17*T)*dist t s,by positivity⟩
      (fun a => supportFlow σ hσ t a-supportFlow σ hσ s a) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hb : ∀r∈Icc 0 T,
      ‖signedClippedField σ (supportFlow σ hσ r a)-signedClippedField σ (supportFlow σ hσ r b)‖≤
        17*exp (17*T)*dist a b := by
    intro r hr
    have hh := (signedClippedField_lipschitz hσ).dist_le_mul
      (supportFlow σ hσ r a) (supportFlow σ hσ r b)
    have hd := supportFlow_distance σ hσ a b hr.1
    have he := mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by linarith [hr.2] : 17*r≤17*T)) (dist_nonneg (x:=a) (y:=b))
    rw [dist_eq_norm] at hh
    norm_num only [NNReal.coe_ofNat] at hh
    nlinarith
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => ((supportFlow_derivative σ hσ a r).sub
      (supportFlow_derivative σ hσ b r)).hasDerivWithinAt) hb (convex_Icc 0 T) hs ht
  change dist _ _≤(17*exp (17*T)*dist t s)*dist a b
  rw [dist_eq_norm]
  have he : supportFlow σ hσ t a-supportFlow σ hσ s a-
      (supportFlow σ hσ t b-supportFlow σ hσ s b)=
      (supportFlow σ hσ t a-supportFlow σ hσ t b)-
      (supportFlow σ hσ s a-supportFlow σ hσ s b) := by abel
  rw [he]
  simpa only [Pi.sub_apply,dist_eq_norm,mul_assoc,mul_left_comm,mul_comm] using hm

theorem supportFlow_fderiv_time_variation (σ : ℝ) (hσ : |σ|≤1) (T : ℝ)
    {s t : ℝ} (hs : s∈Icc 0 T) (ht : t∈Icc 0 T) {a : State}
    (hds : DifferentiableAt ℝ (supportFlow σ hσ s) a)
    (hdt : DifferentiableAt ℝ (supportFlow σ hσ t) a) :
    ‖fderiv ℝ (supportFlow σ hσ t) a-fderiv ℝ (supportFlow σ hσ s) a‖≤
      17*exp (17*T)*dist t s := by
  have hd := hdt.hasFDerivAt.sub hds.hasFDerivAt
  have hb := norm_fderiv_le_of_lipschitz ℝ (x₀:=a) (supportFlow_increment_lipschitz σ hσ T hs ht)
  change ‖fderiv ℝ (supportFlow σ hσ t-supportFlow σ hσ s) a‖≤_ at hb
  rw [hd.fderiv] at hb
  exact hb

theorem supportFlow_joint_lipschitz (σ : ℝ) (hσ : |σ|≤1) (T : ℝ) :
    LipschitzOnWith ⟨exp (17*T)+75,by positivity⟩
      (fun p : ℝ×State => supportFlow σ hσ p.1 p.2) (Icc 0 T ×ˢ univ) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro p hp q hq
  have hs := supportFlow_distance σ hσ p.2 q.2 hp.1.1
  have he := mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (by linarith [hp.1.2] : 17*p.1≤17*T))
    (dist_nonneg (x:=p.2) (y:=q.2))
  have ht := (supportFlow_time_lipschitz σ hσ q.2).dist_le_mul p.1 q.1
  have htri := dist_triangle (supportFlow σ hσ p.1 p.2)
    (supportFlow σ hσ p.1 q.2) (supportFlow σ hσ q.1 q.2)
  have h1 : dist p.1 q.1≤dist p q := le_max_left _ _
  have h2 : dist p.2 q.2≤dist p q := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left h2 (exp_pos (17*T)).le
  norm_num only [NNReal.coe_ofNat] at ht
  change dist _ _≤(exp (17*T)+75)*dist p q
  nlinarith

theorem supportFlow_fderiv_joint_lipschitz (σ : ℝ) (hσ : |σ|≤1) (T : ℝ)
    {c : State} {R : ℝ} (hR : 0<R) (hreg : FlowTubeNeighborhood σ hσ T c R) :
    LipschitzOnWith ⟨(12/17:ℝ)*exp (34*T)+17*exp (17*T),by positivity⟩
      (fun p : ℝ×State => fderiv ℝ (supportFlow σ hσ p.1) p.2)
      (Icc 0 T ×ˢ Metric.ball c (R/4)) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro p hp q hq
  have hqR : q.2∈Metric.ball c R := by
    change dist q.2 c<R
    have h := hq.2
    change dist q.2 c<R/4 at h
    linarith
  have hs := supportFlow_fderiv_space_variation σ hσ hR hreg hp.2 hq.2 hp.1
  have ht := supportFlow_fderiv_time_variation σ hσ T hq.1 hp.1
    (supportFlow_hasFDerivAt_initial σ hσ hreg hqR hq.1).differentiableAt
    (supportFlow_hasFDerivAt_initial σ hσ hreg hqR hp.1).differentiableAt
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (fderiv ℝ (supportFlow σ hσ p.1) p.2)
    (fderiv ℝ (supportFlow σ hσ p.1) q.2)
    (fderiv ℝ (supportFlow σ hσ q.1) q.2)
  have h1 : dist p.1 q.1≤dist p q := le_max_left _ _
  have h2 : dist p.2 q.2≤dist p q := le_max_right _ _
  have hm1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0≤17*exp (17*T))
  have hm2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0≤(12/17:ℝ)*exp (34*T))
  change dist _ _≤((12/17:ℝ)*exp (34*T)+17*exp (17*T))*dist p q
  rw [dist_eq_norm]
  linarith

def supportFlowDifferential (σ : ℝ) (hσ : |σ|≤1) (p : ℝ×State) :
    (ℝ×State) →L[ℝ] State :=
  (ContinuousLinearMap.toSpanSingleton ℝ (signedClippedField σ (supportFlow σ hσ p.1 p.2))).coprod
    (fderiv ℝ (supportFlow σ hσ p.1) p.2)

/-- Genuine joint strict differentiation on an open time/initial-state
neighborhood, obtained solely from the actual ODE and tube confinement. -/
theorem supportFlow_hasStrictFDerivAt_joint (σ : ℝ) (hσ : |σ|≤1) (T : ℝ)
    {c : State} {R : ℝ} (hR : 0<R) (hreg : FlowTubeNeighborhood σ hσ T c R)
    {p : ℝ×State} (hp : p∈Ioo 0 T ×ˢ Metric.ball c (R/4)) :
    HasStrictFDerivAt (fun q : ℝ×State => supportFlow σ hσ q.1 q.2)
      (supportFlowDifferential σ hσ p) p := by
  have hn : Icc (0:ℝ) T ×ˢ Metric.ball c (R/4)∈𝓝 p := by
    apply Filter.mem_of_superset ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds hp)
    intro q hq
    exact ⟨⟨hq.1.1.le,hq.1.2.le⟩,hq.2⟩
  have hn' : Icc (0:ℝ) T ×ˢ (univ : Set State)∈𝓝 p :=
    Filter.mem_of_superset hn (fun _ h => ⟨h.1,mem_univ _⟩)
  have hc : ContinuousAt (fun q : ℝ×State => supportFlow σ hσ q.1 q.2) p :=
    (supportFlow_joint_lipschitz σ hσ T).continuousOn.continuousAt hn'
  have hc₁ : ContinuousAt (fun q : ℝ×State => ContinuousLinearMap.toSpanSingleton ℝ
      (signedClippedField σ (supportFlow σ hσ q.1 q.2))) p :=
    (ContinuousLinearMap.toSpanSingletonCLE : State ≃L[ℝ] (ℝ →L[ℝ] State)).continuous.continuousAt.comp
      ((signedClippedField_lipschitz hσ).continuous.continuousAt.comp hc)
  have hc₂ := (supportFlow_fderiv_joint_lipschitz σ hσ T hR hreg).continuousOn.continuousAt hn
  apply hasStrictFDerivAt_uncurry_coprod (𝕜:=ℝ) (u:=p) (f:=supportFlow σ hσ)
    (f₁:=fun t a => ContinuousLinearMap.toSpanSingleton ℝ (signedClippedField σ (supportFlow σ hσ t a)))
    (f₂:=fun t a => fderiv ℝ (supportFlow σ hσ t) a) ?_ ?_ hc₁ hc₂
  · exact Filter.Eventually.of_forall fun q => (supportFlow_derivative σ hσ q.2 q.1).hasFDerivAt
  · filter_upwards [hn] with q hq
    apply supportFlow_hasFDerivAt_initial σ hσ hreg (t:=q.1) (ht:=hq.1)
    have h := hq.2
    change dist q.2 c<R/4 at h
    change dist q.2 c<R
    linarith

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating joint-flow audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating joint-flow audit passed for {count} declarations."
