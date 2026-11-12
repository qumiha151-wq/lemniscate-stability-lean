import CentroidEscape.MetricShootingDomain
import CentroidEscape.MetricMidpointFlow
import CentroidEscape.MetricBudget

namespace CentroidEscape.MetricStability
noncomputable section
open Set Real Filter
open scoped Topology NNReal
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

lemma weightedField_metric_difference {a b : WeightedState}
    (ha : a∈weightedTube) (hb : b∈weightedTube) :
    metricNorm (weightedField a-weightedField b)≤272*metricNorm (a-b) := by
  have h1 := metricNorm_le_weightedNorm (weightedField a-weightedField b)
  have h2 := lipschitzOnWith_iff_norm_sub_le.mp weightedField_lipschitz ha hb
  have h3 := weightedNorm_le_metricNorm (a-b)
  norm_num only [NNReal.coe_ofNat] at h2
  linarith

theorem shootingFlow_metric_distance_region (T : ℝ) (hT : 0≤T)
    {a b : WeightedState}
    (ha : ∀t∈Icc 0 T, shootingFlow T hT t a∈weightedTube)
    (hb : ∀t∈Icc 0 T, shootingFlow T hT t b∈weightedTube) :
    ∀t∈Icc 0 T, metricNorm (shootingFlow T hT t a-shootingFlow T hT t b)≤
      metricNorm (a-b)*exp ((39/20)*t) := by
  have hh := metric_exact_trajectories hT
    (fun t ht=>(shootingFlow_derivative T hT a ht).continuousAt.continuousWithinAt)
    (fun t ht=>(shootingFlow_derivative T hT b ht).continuousAt.continuousWithinAt)
    (fun t ht=>by
      have hd := shootingFlow_derivative T hT a (Ico_subset_Icc_self ht)
      simpa only [clippedField_eq (ha t (Ico_subset_Icc_self ht))] using hd.hasDerivWithinAt)
    (fun t ht=>by
      have hd := shootingFlow_derivative T hT b (Ico_subset_Icc_self ht)
      simpa only [clippedField_eq (hb t (Ico_subset_Icc_self ht))] using hd.hasDerivWithinAt)
    (fun t ht=>ha t (Ico_subset_Icc_self ht)) (fun t ht=>hb t (Ico_subset_Icc_self ht))
  simpa only [shootingFlow_zero,sub_zero] using hh

def fixedShootingMap (T : ℝ) (hT : 0≤T) (t : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  shootingProjection (shootingFlow T hT t (shootingInitial p))

def fixedShootingDifferential (T : ℝ) (hT : 0≤T) (t : ℝ) (p : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  shootingProjectionLinear.comp ((fderiv ℝ (shootingFlow T hT t) (shootingInitial p)).comp
    shootingInitialLinear)

def fixedShootingVelocity (T : ℝ) (hT : 0≤T) (t : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  shootingProjection (clippedField (shootingFlow T hT t (shootingInitial p)))

lemma shootingInitial_mem_ball {p₀ p : Fin 3 → ℝ} {R : ℝ} (hp : p∈Metric.ball p₀ R) :
    shootingInitial p∈Metric.ball (shootingInitial p₀) R := by
  have hh := shootingInitial_lipschitz.dist_le_mul p p₀
  norm_num only [NNReal.coe_one,one_mul] at hh
  exact hh.trans_lt hp

theorem fixedShootingMap_initial_lipschitz (T : ℝ) (hT : 0≤T)
    {t : ℝ} (ht : t∈Icc 0 T) :
    LipschitzWith (64*(⟨exp (8*t),(exp_pos _).le⟩*1)) (fixedShootingMap T hT t) :=
  shootingProjection_lipschitz.comp ((shootingFlow_initial_lipschitz T hT ht).comp
    shootingInitial_lipschitz)

theorem fixedShootingMap_hasFDerivAt (T : ℝ) (hT : 0≤T)
    {c : WeightedState} {R : ℝ} (hreg : ShootingTubeNeighborhood T hT c R)
    {p : Fin 3 → ℝ} (hp : shootingInitial p∈Metric.ball c R) {t : ℝ} (ht : t∈Icc 0 T) :
    HasFDerivAt (fixedShootingMap T hT t) (fixedShootingDifferential T hT t p) p := by
  have hi : HasFDerivAt shootingInitial shootingInitialLinear p := by
    have hh := (shootingInitialLinear.hasFDerivAt (x:=p)).add_const (shootingInitial 0)
    convert! hh using 1
    funext q
    exact shootingInitial_affine q
  have hh := shootingProjectionLinear.hasFDerivAt.comp p
    ((shootingFlow_hasFDerivAt_initial_region T hT hreg hp ht).comp p hi)
  convert! hh using 1
  funext q
  exact (shootingProjectionLinear_eq _).symm

theorem fixedShootingMap_hasDerivAt_time (T : ℝ) (hT : 0≤T) (p : Fin 3 → ℝ)
    {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivAt (fun s=>fixedShootingMap T hT s p) (fixedShootingVelocity T hT t p) t := by
  have hh := shootingProjectionLinear.hasFDerivAt.comp_hasDerivAt t
    (shootingFlow_derivative T hT (shootingInitial p) ht)
  change HasDerivAt (fun s=>shootingProjectionLinear (shootingFlow T hT s (shootingInitial p)))
    (shootingProjectionLinear (clippedField (shootingFlow T hT t (shootingInitial p)))) t at hh
  simpa only [shootingProjectionLinear_eq,fixedShootingMap,fixedShootingVelocity] using hh

theorem fixedShootingVelocity_initial_difference (T : ℝ) (hT : 0≤T)
    {p₀ : Fin 3 → ℝ} {R : ℝ} (hreg : ShootingTubeNeighborhood T hT (shootingInitial p₀) R)
    {p q : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ R) (hq : q∈Metric.ball p₀ R)
    {t : ℝ} (ht : t∈Icc 0 T) :
    ‖fixedShootingVelocity T hT t p-fixedShootingVelocity T hT t q‖ ≤
      1105*exp ((39/20)*T)*dist p q := by
  have hpT := hreg _ (shootingInitial_mem_ball hp)
  have hqT := hreg _ (shootingInitial_mem_ball hq)
  have hstate := shootingFlow_metric_distance_region T hT hpT hqT t ht
  have hinit := shootingInitial_metric_bound p q
  have he := exp_le_exp.mpr (show (39/20)*t≤(39/20)*T by linarith [ht.2])
  have hm := mul_le_mul hinit he (exp_pos _).le (by positivity)
  have hf := weightedField_metric_difference (hpT t ht) (hqT t ht)
  have hproj := shootingProjection_metric_difference
    (weightedField (shootingFlow T hT t (shootingInitial p)))
    (weightedField (shootingFlow T hT t (shootingInitial q)))
  unfold fixedShootingVelocity
  rw [clippedField_eq (hpT t ht),clippedField_eq (hqT t ht),dist_eq_norm]
  nlinarith

theorem fixedShootingMap_increment_lipschitz (T : ℝ) (hT : 0≤T)
    {p₀ : Fin 3 → ℝ} {R : ℝ} (hreg : ShootingTubeNeighborhood T hT (shootingInitial p₀) R)
    {s t : ℝ} (hs : s∈Icc 0 T) (ht : t∈Icc 0 T) :
    LipschitzOnWith ⟨1105*exp ((39/20)*T)*dist t s,by positivity⟩
      (fun p=>fixedShootingMap T hT t p-fixedShootingMap T hT s p) (Metric.ball p₀ R) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro p hp q hq
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr=>((fixedShootingMap_hasDerivAt_time T hT p hr).sub
      (fixedShootingMap_hasDerivAt_time T hT q hr)).hasDerivWithinAt)
    (fun r hr=>fixedShootingVelocity_initial_difference T hT hreg hp hq hr)
    (convex_Icc 0 T) hs ht
  change dist _ _ ≤ (1105*exp ((39/20)*T)*dist t s)*dist p q
  rw [dist_eq_norm]
  have he : fixedShootingMap T hT t p-fixedShootingMap T hT s p-
      (fixedShootingMap T hT t q-fixedShootingMap T hT s q)=
      (fixedShootingMap T hT t p-fixedShootingMap T hT t q)-
      (fixedShootingMap T hT s p-fixedShootingMap T hT s q) := by abel
  rw [he]
  simpa only [Pi.sub_apply,dist_eq_norm,mul_assoc,mul_left_comm,mul_comm] using hm

theorem fixedShootingDifferential_time_variation (T : ℝ) (hT : 0≤T)
    {p₀ : Fin 3 → ℝ} {R : ℝ} (hreg : ShootingTubeNeighborhood T hT (shootingInitial p₀) R)
    {p : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ R)
    {s t : ℝ} (hs : s∈Icc 0 T) (ht : t∈Icc 0 T) :
    ‖fixedShootingDifferential T hT t p-fixedShootingDifferential T hT s p‖ ≤
      1105*exp ((39/20)*T)*dist t s := by
  have hd := (fixedShootingMap_hasFDerivAt T hT hreg (shootingInitial_mem_ball hp) ht).sub
    (fixedShootingMap_hasFDerivAt T hT hreg (shootingInitial_mem_ball hp) hs)
  have hn := norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hp)
    (fixedShootingMap_increment_lipschitz T hT hreg hs ht)
  change ‖fderiv ℝ (fixedShootingMap T hT t-fixedShootingMap T hT s) p‖ ≤ _ at hn
  rw [hd.fderiv] at hn
  exact hn

lemma shootingInitial_midpoint (p q : Fin 3 → ℝ) :
    shootingInitial ((1/2:ℝ) • (p+q))=(1/2:ℝ) • (shootingInitial p+shootingInitial q) := by
  ext i
  fin_cases i <;> simp [shootingInitial] <;> ring

theorem fixedShootingMap_midpoint (T : ℝ) (hT : 0≤T)
    {p₀ : Fin 3 → ℝ} {R : ℝ} (hreg : ShootingTubeNeighborhood T hT (shootingInitial p₀) R)
    {t : ℝ} (ht : t∈Icc 0 T) :
    ∀ p∈Metric.ball p₀ R, ∀ q∈Metric.ball p₀ R,
      ‖fixedShootingMap T hT t ((1/2:ℝ) • (p+q))-
        (1/2:ℝ) • (fixedShootingMap T hT t p+fixedShootingMap T hT t q)‖ ≤
      ((325/256:ℝ)*exp (2*(39/20)*t))*‖p-q‖^2 := by
  intro p hp q hq
  have hm : (1/2:ℝ) • (p+q)∈Metric.ball p₀ R := by
    simpa only [smul_add] using (convex_ball p₀ R) hp hq
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)+1/2=1)
  have hmid := shootingFlow_metric_midpoint T hT (shootingInitial p) (shootingInitial q)
    (hreg _ (shootingInitial_mem_ball hp)) (hreg _ (shootingInitial_mem_ball hq))
    (by rw [← shootingInitial_midpoint]; exact hreg _ (shootingInitial_mem_ball hm)) t ht
  have hproj := shootingProjection_metric_bound
    ((1/2:ℝ) • (shootingFlow T hT t (shootingInitial p)+shootingFlow T hT t (shootingInitial q))-
      shootingFlow T hT t ((1/2:ℝ) • (shootingInitial p+shootingInitial q)))
  have hinit := (sq_le_sq₀ (metricNorm_nonneg _) (by positivity)).mpr (shootingInitial_metric_bound p q)
  have hprod := mul_le_mul_of_nonneg_left hinit (by positivity : 0≤(5/26:ℝ)*exp (2*(39/20)*t))
  have he : shootingProjection
      ((1/2:ℝ) • (shootingFlow T hT t (shootingInitial p)+shootingFlow T hT t (shootingInitial q))-
        shootingFlow T hT t ((1/2:ℝ) • (shootingInitial p+shootingInitial q))) =
      (1/2:ℝ) • (fixedShootingMap T hT t p+fixedShootingMap T hT t q)-
        fixedShootingMap T hT t ((1/2:ℝ) • (p+q)) := by
    simp only [fixedShootingMap,shootingInitial_midpoint,← shootingProjectionLinear_eq,
      map_sub,map_smul,map_add]
  rw [he,norm_sub_rev] at hproj
  nlinarith

theorem fixedShootingDifferential_space_variation (T : ℝ) (hT : 0≤T)
    {p₀ : Fin 3 → ℝ} {R : ℝ} (hR : 0<R)
    (hreg : ShootingTubeNeighborhood T hT (shootingInitial p₀) R)
    {p q : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ (R/4)) (hq : q∈Metric.ball p₀ (R/4))
    {t : ℝ} (ht : t∈Icc 0 T) :
    ‖fixedShootingDifferential T hT t p-fixedShootingDifferential T hT t q‖ ≤
      (975/32:ℝ)*exp (2*(39/20)*T)*dist p q := by
  have hpR : p∈Metric.ball p₀ R := by
    change dist p p₀<R
    have h : dist p p₀<R/4 := hp
    linarith
  have hqR : q∈Metric.ball p₀ R := by
    change dist q p₀<R
    have h : dist q p₀<R/4 := hq
    linarith
  have hh := quadraticMidpoint_fderiv_variation (fixedShootingMap_initial_lipschitz T hT ht)
    hR (by positivity) (fixedShootingMap_midpoint T hT hreg ht) hp hq
  rw [(fixedShootingMap_hasFDerivAt T hT hreg (shootingInitial_mem_ball hpR) ht).fderiv,
    (fixedShootingMap_hasFDerivAt T hT hreg (shootingInitial_mem_ball hqR) ht).fderiv] at hh
  have he := mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (show 2*(39/20)*t≤2*(39/20)*T by linarith [ht.2]))
    (dist_nonneg (x:=p) (y:=q))
  nlinarith

theorem fixedShootingVelocity_time_difference (T : ℝ) (hT : 0≤T)
    {p₀ : Fin 3 → ℝ} {R : ℝ} (hreg : ShootingTubeNeighborhood T hT (shootingInitial p₀) R)
    {p : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ R)
    {s t : ℝ} (hs : s∈Icc 0 T) (ht : t∈Icc 0 T) :
    ‖fixedShootingVelocity T hT t p-fixedShootingVelocity T hT s p‖ ≤46240*dist t s := by
  have hpT := hreg _ (shootingInitial_mem_ball hp)
  have htime := (shootingFlow_time_lipschitz T hT (shootingInitial p)).dist_le_mul t ht s hs
  have hm := metricNorm_le_weightedNorm
    (shootingFlow T hT t (shootingInitial p)-shootingFlow T hT s (shootingInitial p))
  have hf := weightedField_metric_difference (hpT t ht) (hpT s hs)
  have hproj := shootingProjection_metric_difference
    (weightedField (shootingFlow T hT t (shootingInitial p)))
    (weightedField (shootingFlow T hT s (shootingInitial p)))
  rw [dist_eq_norm] at htime
  norm_num only [NNReal.coe_ofNat] at htime
  unfold fixedShootingVelocity
  rw [clippedField_eq (hpT t ht),clippedField_eq (hpT s hs)]
  linarith

lemma actualShootingDifferential_split (T : ℝ) (hT : 0≤T) (p : Fin 3 → ℝ) :
    actualShootingDifferential T hT p=fixedShootingDifferential T hT (p 2) p+
      (ContinuousLinearMap.toSpanSingleton ℝ (fixedShootingVelocity T hT (p 2) p)).comp
        (ContinuousLinearMap.proj 2) := by
  ext v i
  simp only [actualShootingDifferential,fixedShootingDifferential,shootingFlowDifferential,
    shootingInputLinear,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.proj_apply,ContinuousLinearMap.toSpanSingleton_apply,
    add_apply,map_add,map_smul,shootingProjectionLinear_eq,fixedShootingVelocity]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

def metricShootingJacobianBound (T : ℝ) : ℝ :=
  (975/32:ℝ)*exp (2*(39/20)*T)+2210*exp ((39/20)*T)+46240

theorem actualShootingDifferential_metric_variation (T : ℝ) (hT : 0≤T)
    {p₀ : Fin 3 → ℝ} {R : ℝ} (hR : 0<R)
    (hreg : ShootingTubeNeighborhood T hT (shootingInitial p₀) R)
    {p q : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ (R/4)) (hq : q∈Metric.ball p₀ (R/4))
    (hpt : p 2∈Icc 0 T) (hqt : q 2∈Icc 0 T) :
    ‖actualShootingDifferential T hT p-actualShootingDifferential T hT q‖ ≤
      metricShootingJacobianBound T*dist p q := by
  have hpR : p∈Metric.ball p₀ R := by
    change dist p p₀<R
    have h : dist p p₀<R/4 := hp
    linarith
  have hqR : q∈Metric.ball p₀ R := by
    change dist q p₀<R
    have h : dist q p₀<R/4 := hq
    linarith
  have hDspace := fixedShootingDifferential_space_variation T hT hR hreg hp hq hpt
  have hDtime := fixedShootingDifferential_time_variation T hT hreg hqR hqt hpt
  have hVspace := fixedShootingVelocity_initial_difference T hT hreg hpR hqR hpt
  have hVtime := fixedShootingVelocity_time_difference T hT hreg hqR hqt hpt
  have ht : dist (p 2) (q 2)≤dist p q := by
    simpa only [dist_eq_norm,Pi.sub_apply] using norm_le_pi_norm (p-q) 2
  have hDtri := norm_sub_le_norm_sub_add_norm_sub (fixedShootingDifferential T hT (p 2) p)
    (fixedShootingDifferential T hT (p 2) q) (fixedShootingDifferential T hT (q 2) q)
  have hVtri := norm_sub_le_norm_sub_add_norm_sub (fixedShootingVelocity T hT (p 2) p)
    (fixedShootingVelocity T hT (p 2) q) (fixedShootingVelocity T hT (q 2) q)
  have htE := mul_le_mul_of_nonneg_left ht (by positivity : 0≤1105*exp ((39/20)*T))
  have hsum : ‖fixedShootingDifferential T hT (p 2) p-fixedShootingDifferential T hT (q 2) q‖+
      ‖fixedShootingVelocity T hT (p 2) p-fixedShootingVelocity T hT (q 2) q‖ ≤
        metricShootingJacobianBound T*dist p q := by
    unfold metricShootingJacobianBound
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold metricShootingJacobianBound; positivity)
  intro v
  let D := fixedShootingDifferential T hT (p 2) p-fixedShootingDifferential T hT (q 2) q
  let V := fixedShootingVelocity T hT (p 2) p-fixedShootingVelocity T hT (q 2) q
  have he : (actualShootingDifferential T hT p-actualShootingDifferential T hT q) v=
      D v+(v 2) • V := by
    rw [actualShootingDifferential_split T hT p,actualShootingDifferential_split T hT q]
    dsimp [D,V]
    simp only [sub_apply,add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,ContinuousLinearMap.proj_apply,smul_sub]
    abel
  rw [he]
  have hn := norm_add_le (D v) ((v 2) • V)
  rw [norm_smul] at hn
  have hD := D.le_opNorm v
  have hv := mul_le_mul_of_nonneg_right (norm_le_pi_norm v 2) (norm_nonneg V)
  have hm := mul_le_mul_of_nonneg_right hsum (norm_nonneg v)
  change (‖D‖+‖V‖)*‖v‖≤_ at hm
  nlinarith

theorem actualShootingMap_fderiv_metric_variation (T : ℝ) (hT : 0≤T)
    {p₀ : Fin 3 → ℝ} {R : ℝ} (hR : 0<R)
    (hreg : ShootingTubeNeighborhood T hT (shootingInitial p₀) R)
    {p q : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ (R/4)) (hq : q∈Metric.ball p₀ (R/4))
    (hpt : p 2∈Ioo 0 T) (hqt : q 2∈Ioo 0 T) :
    ‖fderiv ℝ (actualShootingMap T hT) p-fderiv ℝ (actualShootingMap T hT) q‖ ≤
      metricShootingJacobianBound T*dist p q := by
  rw [(actualShootingMap_hasFDerivAt T hT hR hreg hpt (shootingInitial_mem_ball hp)).fderiv,
    (actualShootingMap_hasFDerivAt T hT hR hreg hqt (shootingInitial_mem_ball hq)).fderiv]
  exact actualShootingDifferential_metric_variation T hT hR hreg hp hq
    ⟨hpt.1.le,hpt.2.le⟩ ⟨hqt.1.le,hqt.2.le⟩

theorem metricShootingJacobianBound_budget {T : ℝ} (hT : T≤15/2) :
    metricShootingJacobianBound T<6*10^14 := by
  have he := metric_exp_budget hT
  have hs : (exp ((39/20)*T))^2≤(4000000:ℝ)^2 :=
    (sq_le_sq₀ (exp_pos _).le (by norm_num)).mpr he.le
  have he2 : exp (2*(39/20)*T)=(exp ((39/20)*T))^2 := by
    rw [pow_two,← exp_add]
    congr 1
    ring
  unfold metricShootingJacobianBound
  rw [he2]
  nlinarith

/-- Genuine derivative variation on the actual metric-sized open domain.
All region and differentiability hypotheses come from the interior reference
and its proved short extension. -/
theorem actualShootingMap_fderiv_metric_extended {T : ℝ} (hT : 0<T) {p₀ : Fin 3 → ℝ}
    (hcenter : p₀ 2=T)
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {p q : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ (metricShootingParameterRadius T))
    (hq : q∈Metric.ball p₀ (metricShootingParameterRadius T)) :
    ‖fderiv ℝ (actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le)) p-
      fderiv ℝ (actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le)) q‖ ≤
        metricShootingJacobianBound (shootingExtendedHorizon T)*dist p q := by
  have hp' := metricShootingParameterRadius_domain hcenter hp
  have hq' := metricShootingParameterRadius_domain hcenter hq
  apply actualShootingMap_fderiv_metric_variation _ _ (metricShootingRadius_pos _)
    (shootingFlow_extended_metric_tube T hT.le hc) (hpt:=hp'.1) (hqt:=hq'.1)
  · change dist p p₀<metricShootingRadius T/4
    exact (show dist p p₀<min (metricShootingRadius T/4) (min (T/2) (1/32000)) from hp).trans_le
      (min_le_left _ _)
  · change dist q p₀<metricShootingRadius T/4
    exact (show dist q p₀<min (metricShootingRadius T/4) (min (T/2) (1/32000)) from hq).trans_le
      (min_le_left _ _)

theorem actualShootingMap_fderiv_metric_extended_budget {T : ℝ} (hT : 0<T)
    (hbudget : shootingExtendedHorizon T≤15/2) {p₀ : Fin 3 → ℝ}
    (hcenter : p₀ 2=T)
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {p q : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ (metricShootingParameterRadius T))
    (hq : q∈Metric.ball p₀ (metricShootingParameterRadius T)) :
    ‖fderiv ℝ (actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le)) p-
      fderiv ℝ (actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le)) q‖ ≤
        (6*10^14)*dist p q :=
  (actualShootingMap_fderiv_metric_extended hT hcenter hc hp hq).trans
    (mul_le_mul_of_nonneg_right (metricShootingJacobianBound_budget hbudget).le dist_nonneg)

theorem metricShootingParameterRadius_lower_bound {T : ℝ} (hT : 1≤T)
    (hbudget : shootingExtendedHorizon T≤15/2) :
    (1/10^13:ℝ)<metricShootingParameterRadius T := by
  have he := metric_exp_budget hbudget
  have hR := metricShootingRadius_pos T
  have hprod : metricShootingRadius T*exp ((39/20)*shootingExtendedHorizon T)=3/272000 := by
    rw [metricShootingRadius,mul_assoc,← exp_add]
    ring_nf
    norm_num
  have hm := mul_lt_mul_of_pos_left he hR
  rw [hprod] at hm
  unfold metricShootingParameterRadius
  apply lt_min
  · nlinarith
  · exact lt_min (by norm_num at *; linarith) (by norm_num)

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.fixedShootingDifferential_time_variation
#print axioms CentroidEscape.MetricStability.actualShootingMap_fderiv_metric_extended_budget

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
  logInfo m!"Metric shooting-Jacobian audit passed for {checked} declarations."
