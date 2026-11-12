import CentroidEscape.ShootingDifferentiability
import CentroidEscape.DerivativeVariation
import CentroidEscape.PartialDerivatives

namespace CentroidEscape
noncomputable section
open Set Real Filter
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- A time increment of the ACTUAL flow is Lipschitz in its initial state.
This follows from the ODE and the mean value theorem, without a variational ODE. -/
theorem shootingFlow_increment_lipschitz (T : ℝ) (hT : 0 ≤ T)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    LipschitzWith ⟨8*exp (8*T)*dist t s, by positivity⟩
      (fun a => shootingFlow T hT t a-shootingFlow T hT s a) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hb : ∀ r ∈ Icc 0 T,
      ‖clippedField (shootingFlow T hT r a)-clippedField (shootingFlow T hT r b)‖ ≤
        8*exp (8*T)*dist a b := by
    intro r hr
    have hh := clippedField_lipschitz.dist_le_mul
      (shootingFlow T hT r a) (shootingFlow T hT r b)
    have hd := shootingFlow_distance T hT a b hr
    have he := mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (by linarith [hr.2] : 8*r ≤ 8*T)) (dist_nonneg (x:=a) (y:=b))
    rw [dist_eq_norm] at hh
    norm_num only [NNReal.coe_ofNat] at hh
    nlinarith
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => ((shootingFlow_derivative T hT a hr).sub
      (shootingFlow_derivative T hT b hr)).hasDerivWithinAt)
    hb (convex_Icc 0 T) hs ht
  change dist _ _ ≤ (8*exp (8*T)*dist t s)*dist a b
  rw [dist_eq_norm]
  have he : shootingFlow T hT t a-shootingFlow T hT s a-
      (shootingFlow T hT t b-shootingFlow T hT s b) =
      (shootingFlow T hT t a-shootingFlow T hT t b)-
      (shootingFlow T hT s a-shootingFlow T hT s b) := by abel
  rw [he]
  simpa only [Pi.sub_apply,dist_eq_norm,mul_assoc,mul_left_comm,mul_comm] using hm

/-- The actual initial derivative varies continuously in time wherever it
exists; no differentiability of the globally clipped field is asserted. -/
theorem shootingFlow_fderiv_time_variation (T : ℝ) (hT : 0 ≤ T)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) {a : WeightedState}
    (hds : DifferentiableAt ℝ (shootingFlow T hT s) a)
    (hdt : DifferentiableAt ℝ (shootingFlow T hT t) a) :
    ‖fderiv ℝ (shootingFlow T hT t) a-fderiv ℝ (shootingFlow T hT s) a‖ ≤
      8*exp (8*T)*dist t s := by
  have hd := hdt.hasFDerivAt.sub hds.hasFDerivAt
  have hb := norm_fderiv_le_of_lipschitz ℝ
    (x₀:=a) (shootingFlow_increment_lipschitz T hT hs ht)
  change ‖fderiv ℝ (shootingFlow T hT t-shootingFlow T hT s) a‖ ≤ _ at hb
  rw [hd.fderiv] at hb
  exact hb

/-- Region condition for a whole open family of actual trajectories. -/
def ShootingTubeNeighborhood (T : ℝ) (hT : 0 ≤ T) (c : WeightedState) (R : ℝ) : Prop :=
  ∀ a ∈ Metric.ball c R, ∀ t ∈ Icc 0 T, shootingFlow T hT t a ∈ weightedTube

lemma shootingFlow_local_midpoint (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} {R : ℝ} (hreg : ShootingTubeNeighborhood T hT c R)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ a ∈ Metric.ball c R, ∀ b ∈ Metric.ball c R,
      ‖shootingFlow T hT t ((1/2:ℝ) • (a+b))-
        (1/2:ℝ) • (shootingFlow T hT t a+shootingFlow T hT t b)‖ ≤
        ((11/16:ℝ)*exp (16*t))*‖a-b‖^2 := by
  intro a ha b hb
  have hm := shootingFlow_midpoint_quadratic T hT a b (hreg a ha) (hreg b hb) t ht
  rw [norm_sub_rev] at hm
  simpa only [stateMidpoint,dist_eq_norm] using hm

theorem shootingFlow_hasFDerivAt_initial_region (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} {R : ℝ} (hreg : ShootingTubeNeighborhood T hT c R)
    {a : WeightedState} (ha : a ∈ Metric.ball c R) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasFDerivAt (shootingFlow T hT t) (fderiv ℝ (shootingFlow T hT t) a) a :=
  (quadraticMidpoint_fderiv_at (shootingFlow_initial_lipschitz T hT ht)
    (by positivity) (shootingFlow_local_midpoint T hT hreg ht) ha).1

theorem shootingFlow_fderiv_space_variation (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} {R : ℝ} (hR : 0<R) (hreg : ShootingTubeNeighborhood T hT c R)
    {a b : WeightedState} (ha : a ∈ Metric.ball c (R/4)) (hb : b ∈ Metric.ball c (R/4))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖fderiv ℝ (shootingFlow T hT t) a-fderiv ℝ (shootingFlow T hT t) b‖ ≤
      (33/2:ℝ)*exp (16*T)*dist a b := by
  have hh := quadraticMidpoint_fderiv_variation
    (shootingFlow_initial_lipschitz T hT ht) hR (by positivity)
    (shootingFlow_local_midpoint T hT hreg ht) ha hb
  have he := mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (by linarith [ht.2] : 16*t ≤ 16*T)) (dist_nonneg (x:=a) (y:=b))
  nlinarith

theorem shootingFlow_joint_lipschitz (T : ℝ) (hT : 0 ≤ T) :
    LipschitzOnWith ⟨exp (8*T)+2, by positivity⟩
      (fun p : ℝ × WeightedState => shootingFlow T hT p.1 p.2) (Icc 0 T ×ˢ univ) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro p hp q hq
  have hs := shootingFlow_distance T hT p.2 q.2 hp.1
  have he := mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (by linarith [hp.1.2] : 8*p.1 ≤ 8*T))
    (dist_nonneg (x:=p.2) (y:=q.2))
  have ht := (shootingFlow_time_lipschitz T hT q.2).dist_le_mul p.1 hp.1 q.1 hq.1
  have htri := dist_triangle (shootingFlow T hT p.1 p.2)
    (shootingFlow T hT p.1 q.2) (shootingFlow T hT q.1 q.2)
  have h1 : dist p.1 q.1 ≤ dist p q := le_max_left _ _
  have h2 : dist p.2 q.2 ≤ dist p q := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left h2 (exp_pos (8*T)).le
  norm_num only [NNReal.coe_ofNat] at ht
  change dist _ _ ≤ (exp (8*T)+2)*dist p q
  nlinarith

theorem shootingFlow_fderiv_joint_lipschitz (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} {R : ℝ} (hR : 0<R) (hreg : ShootingTubeNeighborhood T hT c R) :
    LipschitzOnWith ⟨(33/2:ℝ)*exp (16*T)+8*exp (8*T), by positivity⟩
      (fun p : ℝ × WeightedState => fderiv ℝ (shootingFlow T hT p.1) p.2)
      (Icc 0 T ×ˢ Metric.ball c (R/4)) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro p hp q hq
  have hqR : q.2 ∈ Metric.ball c R := by
    change dist q.2 c<R
    have h := hq.2
    change dist q.2 c<R/4 at h
    linarith
  have hs := shootingFlow_fderiv_space_variation T hT hR hreg hp.2 hq.2 hp.1
  have ht := shootingFlow_fderiv_time_variation T hT hq.1 hp.1
    (shootingFlow_hasFDerivAt_initial_region T hT hreg hqR hq.1).differentiableAt
    (shootingFlow_hasFDerivAt_initial_region T hT hreg hqR hp.1).differentiableAt
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (fderiv ℝ (shootingFlow T hT p.1) p.2)
    (fderiv ℝ (shootingFlow T hT p.1) q.2)
    (fderiv ℝ (shootingFlow T hT q.1) q.2)
  have h1 : dist p.1 q.1 ≤ dist p q := le_max_left _ _
  have h2 : dist p.2 q.2 ≤ dist p q := le_max_right _ _
  have hm1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 8*exp (8*T))
  have hm2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (33/2:ℝ)*exp (16*T))
  change dist _ _ ≤ ((33/2:ℝ)*exp (16*T)+8*exp (8*T))*dist p q
  rw [dist_eq_norm]
  linarith

def shootingFlowDifferential (T : ℝ) (hT : 0 ≤ T) (p : ℝ × WeightedState) :
    (ℝ × WeightedState) →L[ℝ] WeightedState :=
  (ContinuousLinearMap.toSpanSingleton ℝ (clippedField (shootingFlow T hT p.1 p.2))).coprod
    (fderiv ℝ (shootingFlow T hT p.1) p.2)

/-- The actual flow has a genuine joint time/initial-state derivative on an
OPEN time interval. Endpoint differentiation is deliberately not inferred. -/
theorem shootingFlow_hasFDerivAt_joint (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} {R : ℝ} (hR : 0<R) (hreg : ShootingTubeNeighborhood T hT c R)
    {p : ℝ × WeightedState} (hp : p ∈ Ioo 0 T ×ˢ Metric.ball c (R/4)) :
    HasFDerivAt (fun q : ℝ × WeightedState => shootingFlow T hT q.1 q.2)
      (shootingFlowDifferential T hT p) p := by
  have hn : Icc (0:ℝ) T ×ˢ Metric.ball c (R/4) ∈ 𝓝 p := by
    apply Filter.mem_of_superset ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds hp)
    intro q hq
    exact ⟨⟨hq.1.1.le,hq.1.2.le⟩,hq.2⟩
  have hn' : Icc (0:ℝ) T ×ˢ (univ : Set WeightedState) ∈ 𝓝 p :=
    Filter.mem_of_superset hn (fun _ h => ⟨h.1,mem_univ _⟩)
  have hc : ContinuousAt (fun q : ℝ × WeightedState => shootingFlow T hT q.1 q.2) p :=
    (shootingFlow_joint_lipschitz T hT).continuousOn.continuousAt hn'
  have hc₁ : ContinuousAt (fun q : ℝ × WeightedState => ContinuousLinearMap.toSpanSingleton ℝ
      (clippedField (shootingFlow T hT q.1 q.2))) p :=
    (ContinuousLinearMap.toSpanSingletonCLE : WeightedState ≃L[ℝ] (ℝ →L[ℝ] WeightedState)).continuous.continuousAt.comp
      (clippedField_lipschitz.continuous.continuousAt.comp hc)
  have hc₂ := (shootingFlow_fderiv_joint_lipschitz T hT hR hreg).continuousOn.continuousAt hn
  apply (hasStrictFDerivAt_uncurry_coprod (𝕜:=ℝ) (u:=p)
    (f:=shootingFlow T hT)
    (f₁:=fun t a => ContinuousLinearMap.toSpanSingleton ℝ (clippedField (shootingFlow T hT t a)))
    (f₂:=fun t a => fderiv ℝ (shootingFlow T hT t) a) ?_ ?_ hc₁ hc₂).hasFDerivAt
  · filter_upwards [hn] with q hq
    exact (shootingFlow_derivative T hT q.2 hq.1).hasFDerivAt
  · filter_upwards [hn] with q hq
    apply shootingFlow_hasFDerivAt_initial_region T hT hreg (t:=q.1) (ht:=hq.1)
    have h := hq.2
    change dist q.2 c<R/4 at h
    change dist q.2 c<R
    linarith

def shootingInitialLinear : (Fin 3 → ℝ) →L[ℝ] WeightedState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,0,0,0,
    (1/16:ℝ) • ContinuousLinearMap.proj 1,0,0]

def shootingProjectionLinear : WeightedState →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 1,
    (4:ℝ) • ContinuousLinearMap.proj 2,(64:ℝ) • ContinuousLinearMap.proj 5]

def shootingInputLinear : (Fin 3 → ℝ) →L[ℝ] (ℝ × WeightedState) :=
  (ContinuousLinearMap.proj 2).prod shootingInitialLinear

lemma shootingProjectionLinear_eq (z : WeightedState) :
    shootingProjectionLinear z=shootingProjection z := by
  ext i
  fin_cases i <;> simp [shootingProjectionLinear,shootingProjection]

lemma shootingInitial_affine (p : Fin 3 → ℝ) :
    shootingInitial p=shootingInitialLinear p+shootingInitial 0 := by
  ext i
  fin_cases i <;> simp [shootingInitialLinear,shootingInitial,div_eq_mul_inv,mul_comm]

lemma shootingInput_hasFDerivAt (p : Fin 3 → ℝ) :
    HasFDerivAt (fun q => (q 2,shootingInitial q)) shootingInputLinear p := by
  have hh := (shootingInputLinear.hasFDerivAt (x:=p)).add_const ((0:ℝ),shootingInitial 0)
  convert! hh using 1
  funext q
  simp [shootingInputLinear,← shootingInitial_affine]

def actualShootingDifferential (T : ℝ) (hT : 0 ≤ T) (p : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  shootingProjectionLinear.comp ((shootingFlowDifferential T hT (p 2,shootingInitial p)).comp
    shootingInputLinear)

/-- The actual three-parameter shooting map, including the terminal-time
parameter L, is genuinely Frechet differentiable on its proved open domain. -/
theorem actualShootingMap_hasFDerivAt (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} {R : ℝ} (hR : 0<R) (hreg : ShootingTubeNeighborhood T hT c R)
    {p : Fin 3 → ℝ} (ht : p 2 ∈ Ioo 0 T) (hp : shootingInitial p ∈ Metric.ball c (R/4)) :
    HasFDerivAt (actualShootingMap T hT) (actualShootingDifferential T hT p) p := by
  have hh := shootingProjectionLinear.hasFDerivAt.comp p
    ((shootingFlow_hasFDerivAt_joint T hT hR hreg ⟨ht,hp⟩).comp p
      (shootingInput_hasFDerivAt p))
  convert! hh using 1
  funext q
  change shootingProjection _=shootingProjectionLinear _
  exact (shootingProjectionLinear_eq _).symm

lemma shootingInitialLinear_bound (p : Fin 3 → ℝ) : ‖shootingInitialLinear p‖ ≤ ‖p‖ := by
  have hh := shootingInitial_lipschitz.norm_sub_le p 0
  rw [shootingInitial_affine p,add_sub_cancel_right] at hh
  simpa only [NNReal.coe_one,one_mul,sub_zero] using hh

lemma shootingInputLinear_bound (p : Fin 3 → ℝ) : ‖shootingInputLinear p‖ ≤ ‖p‖ := by
  change max ‖p 2‖ ‖shootingInitialLinear p‖ ≤ ‖p‖
  exact max_le (norm_le_pi_norm p 2) (shootingInitialLinear_bound p)

lemma shootingProjectionLinear_bound (z : WeightedState) :
    ‖shootingProjectionLinear z‖ ≤ 64*‖z‖ := by
  have hh := shootingProjection_lipschitz.norm_sub_le z 0
  have hz : shootingProjection 0=0 := by ext i; fin_cases i <;> simp [shootingProjection]
  simpa only [shootingProjectionLinear_eq,hz,sub_zero,NNReal.coe_ofNat] using hh

def shootingJacobianVariationBound (T : ℝ) : ℝ :=
  (33/2:ℝ)*exp (16*T)+16*exp (8*T)+16

theorem shootingFlowDifferential_variation (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} {R : ℝ} (hR : 0<R) (hreg : ShootingTubeNeighborhood T hT c R)
    {p q : ℝ × WeightedState}
    (hp : p ∈ Icc 0 T ×ˢ Metric.ball c (R/4))
    (hq : q ∈ Icc 0 T ×ˢ Metric.ball c (R/4)) :
    ‖shootingFlowDifferential T hT p-shootingFlowDifferential T hT q‖ ≤
      shootingJacobianVariationBound T*dist p q := by
  have hstate := (shootingFlow_joint_lipschitz T hT).dist_le_mul p ⟨hp.1,mem_univ _⟩
    q ⟨hq.1,mem_univ _⟩
  have hg := clippedField_lipschitz.dist_le_mul
    (shootingFlow T hT p.1 p.2) (shootingFlow T hT q.1 q.2)
  have hA := (shootingFlow_fderiv_joint_lipschitz T hT hR hreg).dist_le_mul p hp q hq
  simp only [dist_eq_norm,NNReal.coe_ofNat] at hg
  rw [dist_eq_norm] at hA
  change ‖fderiv ℝ (shootingFlow T hT p.1) p.2-fderiv ℝ (shootingFlow T hT q.1) q.2‖ ≤
    ((33/2:ℝ)*exp (16*T)+8*exp (8*T))*dist p q at hA
  change dist _ _ ≤ (exp (8*T)+2)*dist p q at hstate
  rw [dist_eq_norm (shootingFlow T hT p.1 p.2) (shootingFlow T hT q.1 q.2)] at hstate
  have hg' : ‖clippedField (shootingFlow T hT p.1 p.2)-
      clippedField (shootingFlow T hT q.1 q.2)‖ ≤ 8*(exp (8*T)+2)*dist p q := by
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold shootingJacobianVariationBound; positivity)
  intro v
  let gp := clippedField (shootingFlow T hT p.1 p.2)
  let gq := clippedField (shootingFlow T hT q.1 q.2)
  let Ap := fderiv ℝ (shootingFlow T hT p.1) p.2
  let Aq := fderiv ℝ (shootingFlow T hT q.1) q.2
  have he : (shootingFlowDifferential T hT p-shootingFlowDifferential T hT q) v =
      v.1 • (gp-gq)+(Ap-Aq) v.2 := by
    simp only [shootingFlowDifferential,sub_apply,ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply,smul_sub]
    dsimp [gp,gq,Ap,Aq]
    abel
  rw [he]
  have hn := norm_add_le (v.1 • (gp-gq)) ((Ap-Aq) v.2)
  have hm := (Ap-Aq).le_opNorm v.2
  have h1 := norm_fst_le v
  have h2 := norm_snd_le v
  rw [norm_smul] at hn
  have hm1 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (gp-gq))
  have hm2 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (Ap-Aq))
  have hmg := mul_le_mul_of_nonneg_right hg' (norm_nonneg v)
  have hmA := mul_le_mul_of_nonneg_right hA (norm_nonneg v)
  change ‖gp-gq‖*‖v‖ ≤ _ at hmg
  change ‖Ap-Aq‖*‖v‖ ≤ _ at hmA
  dsimp [shootingJacobianVariationBound]
  nlinarith

theorem actualShootingDifferential_variation (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} {R : ℝ} (hR : 0<R) (hreg : ShootingTubeNeighborhood T hT c R)
    {p q : Fin 3 → ℝ} (hpt : p 2 ∈ Icc 0 T) (hqt : q 2 ∈ Icc 0 T)
    (hp : shootingInitial p ∈ Metric.ball c (R/4)) (hq : shootingInitial q ∈ Metric.ball c (R/4)) :
    ‖actualShootingDifferential T hT p-actualShootingDifferential T hT q‖ ≤
      64*shootingJacobianVariationBound T*dist p q := by
  have hb := shootingFlowDifferential_variation T hT hR hreg
    (p:=(p 2,shootingInitial p)) (q:=(q 2,shootingInitial q)) ⟨hpt,hp⟩ ⟨hqt,hq⟩
  have hin : dist (p 2,shootingInitial p) (q 2,shootingInitial q) ≤ dist p q := by
    change max (dist (p 2) (q 2)) (dist (shootingInitial p) (shootingInitial q)) ≤ dist p q
    apply max_le
    · simpa only [dist_eq_norm,Pi.sub_apply] using norm_le_pi_norm (p-q) 2
    · simpa only [NNReal.coe_one,one_mul] using shootingInitial_lipschitz.dist_le_mul p q
  have hB : 0 ≤ shootingJacobianVariationBound T := by unfold shootingJacobianVariationBound; positivity
  have hbound := hb.trans (mul_le_mul_of_nonneg_left hin hB)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : (actualShootingDifferential T hT p-actualShootingDifferential T hT q) v =
      shootingProjectionLinear ((shootingFlowDifferential T hT (p 2,shootingInitial p)-
        shootingFlowDifferential T hT (q 2,shootingInitial q)) (shootingInputLinear v)) := by
    simp [actualShootingDifferential,map_sub]
  rw [he]
  have hproj := shootingProjectionLinear_bound
    ((shootingFlowDifferential T hT (p 2,shootingInitial p)-
        shootingFlowDifferential T hT (q 2,shootingInitial q)) (shootingInputLinear v))
  have hm := (shootingFlowDifferential T hT (p 2,shootingInitial p)-
        shootingFlowDifferential T hT (q 2,shootingInitial q)).le_opNorm (shootingInputLinear v)
  have hm' := mul_le_mul hbound (shootingInputLinear_bound v) (norm_nonneg _) (by positivity)
  nlinarith

theorem actualShootingMap_fderiv_variation (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} {R : ℝ} (hR : 0<R) (hreg : ShootingTubeNeighborhood T hT c R)
    {p q : Fin 3 → ℝ} (hpt : p 2 ∈ Ioo 0 T) (hqt : q 2 ∈ Ioo 0 T)
    (hp : shootingInitial p ∈ Metric.ball c (R/4)) (hq : shootingInitial q ∈ Metric.ball c (R/4)) :
    ‖fderiv ℝ (actualShootingMap T hT) p-fderiv ℝ (actualShootingMap T hT) q‖ ≤
      64*shootingJacobianVariationBound T*dist p q := by
  rw [(actualShootingMap_hasFDerivAt T hT hR hreg hpt hp).fderiv,
    (actualShootingMap_hasFDerivAt T hT hR hreg hqt hq).fderiv]
  exact actualShootingDifferential_variation T hT hR hreg
    ⟨hpt.1.le,hpt.2.le⟩ ⟨hqt.1.le,hqt.2.le⟩ hp hq

end
end CentroidEscape

#print axioms CentroidEscape.shootingFlow_fderiv_space_variation
#print axioms CentroidEscape.actualShootingMap_hasFDerivAt
#print axioms CentroidEscape.actualShootingMap_fderiv_variation

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Shooting-Jacobian audit passed for {checked} declarations."
