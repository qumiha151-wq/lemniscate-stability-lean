import Lemniscate.BernoulliCombinedEnergyEstimate
import Lemniscate.BernoulliCoverModulationData
import Lemniscate.PeriodicParabolicH2EnergyIdentity
import Lemniscate.PeriodicParabolicEstimates
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Decay of actual maximal-regularity solutions of the modulated equation.

The phase condition is propagated using the actual Bochner primitive.
The two proved quadratic energy identities yield an absolutely continuous
scalar energy; an integrating factor then gives decay and dissipation.
-/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set CoarseArithmetic
open scoped ENNReal Topology ComplexConjugate

private theorem clm_unit_primitive
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) (τ : ℝ) (q v : unitInterval → E)
    (hv : Integrable v volume)
    (hq : ∀ t, q t-q 0 = τ • (∫ r in Iic t, v r ∂volume)) (t : unitInterval) :
    L (q t)-L (q 0) = τ • (∫ r in Iic t, L (v r) ∂volume) := by
  calc
    L (q t)-L (q 0) = L (q t-q 0) := (map_sub L _ _).symm
    _ = L (τ • (∫ r in Iic t, v r ∂volume)) := congrArg L (hq t)
    _ = τ • (∫ r in Iic t, L (v r) ∂volume) := by
      change (L.restrictScalars ℝ) (τ • (∫ r in Iic t, v r ∂volume)) = _
      rw [map_smul,← (L.restrictScalars ℝ).integral_comp_comm hv.integrableOn]
      simp only [ContinuousLinearMap.coe_restrictScalars']

private theorem scalar_energy_add
    {a₀ a₁ b₀ b₁ z I J κ : ℝ}
    (ha : a₁-a₀ = z*I) (hb : b₁-b₀ = z*J) :
    (a₁+κ*b₁)-(a₀+κ*b₀) = z*(I+κ*J) := by
  linear_combination ha+κ*hb

private theorem scale_energy_bound {z e E D μ c : ℝ}
    (hz : 0 ≤ z) (h : e ≤ -μ*E-c*D) :
    z*e ≤ -(z*μ)*E-(z*c)*D := by
  calc
    z*e ≤ z*(-μ*E-c*D) := mul_le_mul_of_nonneg_left h hz
    _ = -(z*μ)*E-(z*c)*D := by ring

private theorem unit_interval_energy_decay
    (E J D : unitInterval → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hE : ∀ t, 0 ≤ E t) (hD : ∀ t, 0 ≤ D t)
    (hJint : Integrable J volume) (hDint : Integrable D volume)
    (hprimitive : ∀ t, E t-E 0 = ∫ r in Iic t, J r ∂volume)
    (hbound : ∀ᵐ t ∂volume, J t ≤ -a*E t-b*D t) :
    ∀ t : unitInterval,
      E t ≤ Real.exp (-a*(t:ℝ))*E 0 ∧
      b*(∫ r in Iic t, D r ∂volume) ≤ E 0 := by
  let clamp : ℝ → unitInterval := Set.projIcc (0:ℝ) 1 zero_le_one
  have hclamp (t : unitInterval) : clamp (t:ℝ) = t := Set.projIcc_val zero_le_one t
  let j : ℝ → ℝ := fun r => J (clamp r)
  have hjOn : IntegrableOn j (Icc (0:ℝ) 1) volume := by
    apply (unitInterval.measurePreserving_coe.integrable_comp_emb
      unitInterval.measurableEmbedding_coe).mp
    simpa only [Function.comp_def,j,hclamp] using hJint
  have hj : IntervalIntegrable j volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hjOn
  let P : ℝ → ℝ := fun r => E 0+∫ s in (0:ℝ)..r, j s
  have hP (t : unitInterval) : P (t:ℝ) = E t := by
    have hp := hprimitive t
    have hi : (∫ r in Iic t, j (r:ℝ) ∂volume) = ∫ r in Iic t, J r ∂volume := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro r _
      simp only [j,hclamp]
    change E 0+(∫ r in (0:ℝ)..(t:ℝ), j r) = E t
    rw [← unit_interval_setIntegral j t,hi,← hp]
    ring
  have hconstant : AbsolutelyContinuousOnInterval (fun _ : ℝ => E 0) 0 1 :=
    (show ContDiffOn ℝ 1 (fun _ : ℝ => E 0) (uIcc 0 1) from
      contDiff_const.contDiffOn).absolutelyContinuousOnInterval
  have hPac : AbsolutelyContinuousOnInterval P 0 1 :=
    hconstant.fun_add (hj.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hexpOn : ContDiffOn ℝ 1 (fun r : ℝ => Real.exp (a*r)) (uIcc 0 1) :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have hexp : AbsolutelyContinuousOnInterval (fun r : ℝ => Real.exp (a*r)) 0 1 :=
    ContDiffOn.absolutelyContinuousOnInterval hexpOn
  let W : ℝ → ℝ := fun r => Real.exp (a*r)*P r
  have hWac : AbsolutelyContinuousOnInterval W 0 1 := hexp.fun_mul hPac
  have hBrestrict : ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) 1),
      j r ≤ -a*P r-b*D (clamp r) := by
    rw [← unitInterval.measurePreserving_coe.map_eq]
    apply unitInterval.measurableEmbedding_coe.ae_map_iff.mpr
    filter_upwards [hbound] with t ht
    simpa only [j,hclamp,hP] using ht
  have hB : ∀ᵐ r ∂volume, r ∈ uIcc (0:ℝ) 1 → j r ≤ -a*P r-b*D (clamp r) := by
    rw [uIcc_of_le zero_le_one]
    exact (ae_restrict_iff' measurableSet_Icc).mp hBrestrict
  have hWderiv : ∀ᵐ r ∂volume, r ∈ uIcc (0:ℝ) 1 → deriv W r ≤ 0 := by
    filter_upwards [hj.ae_hasDerivAt_integral,hB] with r hr hBr hmem
    have hPr : HasDerivAt P (j r) r := (hr hmem 0 (by simp)).const_add (E 0)
    have hEr : HasDerivAt (fun s : ℝ => Real.exp (a*s))
        (Real.exp (a*r)*a) r := by
      convert! (Real.hasDerivAt_exp (a*r)).comp r ((hasDerivAt_id r).const_mul a) using 1 <;> ring
    have hWr : HasDerivAt W (Real.exp (a*r)*(j r+a*P r)) r := by
      convert! hEr.mul hPr using 1 <;> ring
    rw [hWr.deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hbd : 0 ≤ b*D (clamp r) := mul_nonneg hb.le (hD _)
    linarith only [hBr hmem,hbd]
  intro t
  have hWtac : AbsolutelyContinuousOnInterval W 0 (t:ℝ) :=
    hWac.mono (uIcc_subset_uIcc (by simp) (by
      simpa only [uIcc_of_le zero_le_one] using t.property))
  have hWint : (∫ r in (0:ℝ)..(t:ℝ), deriv W r) ≤ 0 := by
    rw [intervalIntegral.integral_of_le t.property.1]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_of_ae hWderiv,ae_restrict_mem measurableSet_Ioc] with r hr hrt
    exact hr (by rw [uIcc_of_le zero_le_one]; exact ⟨hrt.1.le,hrt.2.trans t.property.2⟩)
  have hEW : Real.exp (a*(t:ℝ))*E t ≤ E 0 := by
    have hd : W (t:ℝ)-W 0 ≤ 0 := by rw [← hWtac.integral_deriv_eq_sub]; exact hWint
    have heq : W 0 = E 0 := by simp [W,P]
    have htEq : W (t:ℝ) = Real.exp (a*(t:ℝ))*E t :=
      congrArg (Real.exp (a*(t:ℝ))*·) (hP t)
    have hle := sub_nonpos.mp hd
    rwa [htEq,heq] at hle
  have hdecay : E t ≤ Real.exp (-a*(t:ℝ))*E 0 := by
    calc
      E t = Real.exp (-a*(t:ℝ))*(Real.exp (a*(t:ℝ))*E t) := by
        rw [← mul_assoc,← Real.exp_add]
        simp
      _ ≤ Real.exp (-a*(t:ℝ))*E 0 :=
        mul_le_mul_of_nonneg_left hEW (Real.exp_pos _).le
  have hJle : ∀ᵐ r ∂volume, J r ≤ (-b)*D r := by
    filter_upwards [hbound] with r hr
    have hp : 0 ≤ a*E r := mul_nonneg ha.le (hE r)
    linarith only [hr,hp]
  have hi := integral_mono_ae hJint.integrableOn (hDint.const_mul (-b)).integrableOn
    (ae_restrict_of_ae hJle : ∀ᵐ r ∂volume.restrict (Iic t), J r ≤ (-b)*D r)
  rw [integral_const_mul] at hi
  refine ⟨hdecay,?_⟩
  linarith only [hi,hprimitive t,hE t]

section Parabolic
variable (S : ℝ) [Fact (0 < S)]

set_option maxHeartbeats 1200000 in
private theorem parabolic_modulated_decay
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (ψ : CircleL2 S)
    (V : CircleL2 S →L[ℂ] CircleL2 S) (κ δ μ c : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hμ : 0 < μ) (hc : 0 < c)
    (hzero : ∀ f : CircleSobolevSpace S 4,
      ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖ < δ →
      inner ℂ ψ (circleNormalGraphModulatedFlow S K (15/2) ψ f) = 0)
    (hpoint : ∀ f : CircleSobolevSpace S 4,
      inner ℂ ψ (circleSobolevCoordinate S 4 0 f) = 0 →
      ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖ < δ →
      (inner ℂ (circleSobolevPrincipalOperator S f)
        (circleNormalGraphModulatedFlow S K (15/2) ψ f)).re+
        κ*(inner ℂ (V (circleSobolevCoordinate S 4 0 f))
          (V (circleNormalGraphModulatedFlow S K (15/2) ψ f))).re ≤
        -μ*(‖circleSobolevCoordinate S 4 0 f‖^2+
          4*‖circleSobolevCoordinate S 4 2 f‖^2+
          κ*‖V (circleSobolevCoordinate S 4 0 f)‖^2)-c*‖f‖^2)
    (τ : ℝ) (hτ : 0 < τ) (U : CircleParabolicSpace S τ)
    (hinit : inner ℂ ψ (circleSobolevCoordinate S 2 0 (circleParabolicInitialValue S τ U)) = 0)
    (hsmall : ‖circleParabolicCurve S τ U‖ < δ)
    (hPDE : ∀ᵐ r : unitInterval ∂volume,
      circleParabolicTimeDerivative S τ U r =
        circleNormalGraphModulatedFlow S K (15/2) ψ (circleParabolicH4 S τ U r)) :
    let E : unitInterval → ℝ := fun r =>
      ‖circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r)‖^2+
        4*‖circleSobolevCoordinate S 2 2 (circleParabolicCurve S τ U r)‖^2+
        κ*‖V (circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r))‖^2
    (∀ r : unitInterval,
      inner ℂ ψ (circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r)) = 0) ∧
      ∀ t : unitInterval, E t ≤ Real.exp (-2*τ*μ*(t:ℝ))*E 0 ∧
        (2*τ*c)*(∫ r in Iic t, ‖circleParabolicH4 S τ U r‖^2 ∂volume) ≤ E 0 := by
  let q : unitInterval → CircleL2 S :=
    fun r => circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r)
  let d : unitInterval → CircleL2 S :=
    fun r => circleSobolevCoordinate S 2 2 (circleParabolicCurve S τ U r)
  let f := circleParabolicH4 S τ U
  let v := circleParabolicTimeDerivative S τ U
  let A : CircleTimeL2 S := (circleSobolevPrincipalOperator S).compLpL 2 volume f
  let w : CircleTimeL2 S := (circleSobolevCoordinate S 4 0).compLpL 2 volume f
  let Vw : CircleTimeL2 S := V.compLpL 2 volume w
  let Vv : CircleTimeL2 S := V.compLpL 2 volume v
  let E : unitInterval → ℝ := fun r => ‖q r‖^2+4*‖d r‖^2+κ*‖V (q r)‖^2
  let e : unitInterval → ℝ := fun r =>
    (inner ℂ (A r) (v r)).re+κ*(inner ℂ (Vw r) (Vv r)).re
  have hv : Integrable (v : unitInterval → CircleL2 S) volume :=
    circle_parabolic_time_derivative_integrable S τ U
  have hq : ∀ r, q r-q 0 = τ • (∫ s in Iic r, v s ∂volume) :=
    circle_parabolic_integral_identity S τ U
  have hlow := circle_parabolic_h2_h4_ae S τ U
  have hval := circle_parabolic_value_ae S τ U
  have hA := (circleSobolevPrincipalOperator S).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) f
  have hw := (circleSobolevCoordinate S 4 0).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) f
  have hVw := V.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval)) w
  have hVv := V.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval)) v
  have hsmallAE : ∀ᵐ r ∂volume,
      ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 (f r))‖ < δ := by
    filter_upwards [hlow] with r hr
    have hn := congrArg (fun z : CircleSobolevSpace S 2 => ‖z‖) hr
    exact hn.symm.le.trans_lt
      (((circleParabolicCurve S τ U).norm_coe_le_norm r).trans_lt hsmall)
  have hvzero : ∀ᵐ r ∂volume, inner ℂ ψ (v r) = 0 := by
    filter_upwards [hPDE,hsmallAE] with r hr hs
    exact (congrArg (fun z => inner ℂ ψ z) hr).trans (hzero (f r) hs)
  have hphase (t : unitInterval) : inner ℂ ψ (q t) = 0 := by
    have ht := clm_unit_primitive (innerSL ℂ ψ) τ q v hv hq t
    have hi : (∫ r in Iic t, inner ℂ ψ (v r) ∂volume) = 0 :=
      integral_eq_zero_of_ae (ae_restrict_of_ae hvzero)
    simp only [innerSL_apply_apply] at ht
    rw [hi,smul_zero] at ht
    have h0 : inner ℂ ψ (q 0) = 0 := hinit
    rw [h0,sub_zero] at ht
    exact ht
  have hintA : Integrable (fun r => (inner ℂ (A r) (v r)).re) volume := by
    simpa only [RCLike.reCLM_apply,RCLike.re_eq_complex_re] using
      (RCLike.reCLM : ℂ →L[ℝ] ℝ).integrable_comp (L2.integrable_inner (𝕜 := ℂ) A v)
  have hintV : Integrable (fun r => (inner ℂ (Vw r) (Vv r)).re) volume := by
    simpa only [RCLike.reCLM_apply,RCLike.re_eq_complex_re] using
      (RCLike.reCLM : ℂ →L[ℝ] ℝ).integrable_comp (L2.integrable_inner (𝕜 := ℂ) Vw Vv)
  have hinte : Integrable e volume := hintA.add (hintV.const_mul κ)
  have henergy (t : unitInterval) : E t-E 0 = (2*τ)*(∫ r in Iic t, e r ∂volume) := by
    have h1 := circle_parabolic_h2_energy_identity S τ U t
    have h2 := unit_interval_primitive_norm_sq_energy τ (fun r => V (q r))
      (fun r => V (v r)) (V.integrable_comp hv) (clm_unit_primitive V τ q v hv hq) t
    have hI1 : (∫ r in Iic t,
        (inner ℂ (circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r)+
          (4:ℂ) • circleSobolevCoordinate S 4 4 (f r)) (v r)).re ∂volume) =
        ∫ r in Iic t, (inner ℂ (A r) (v r)).re ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hval,ae_restrict_of_ae hA] with r hr hAr
      rw [hr,hAr] <;> rfl
    have hI2 : (∫ r in Iic t, (inner ℂ (V (q r)) (V (v r))).re ∂volume) =
        ∫ r in Iic t, (inner ℂ (Vw r) (Vv r)).re ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hval,ae_restrict_of_ae hw,
        ae_restrict_of_ae hVw,ae_restrict_of_ae hVv] with r hr hwr hVwr hVvr
      have heq : V (q r) = Vw r :=
        (congrArg V (hr.trans hwr.symm)).trans hVwr.symm
      exact congrArg₂ (fun a b : CircleL2 S => (inner ℂ a b).re) heq hVvr.symm
    have h1' := h1.trans (congrArg ((2*τ)*·) hI1)
    have h2' := h2.trans (congrArg ((2*τ)*·) hI2)
    have hs := scalar_energy_add (κ := κ) h1' h2'
    have hi : (∫ r in Iic t, e r ∂volume) =
        (∫ r in Iic t, (inner ℂ (A r) (v r)).re ∂volume)+
          κ*(∫ r in Iic t, (inner ℂ (Vw r) (Vv r)).re ∂volume) := by
      exact (integral_add hintA.integrableOn (hintV.const_mul κ).integrableOn).trans
        (congrArg ((∫ r in Iic t, (inner ℂ (A r) (v r)).re ∂volume)+·)
          (integral_const_mul κ _))
    exact hs.trans (congrArg ((2*τ)*·) hi.symm)
  have hpointAE : ∀ᵐ r ∂volume, e r ≤ -μ*E r-c*‖f r‖^2 := by
    filter_upwards [hPDE,hlow,hval,hsmallAE,hA,hw,hVw,hVv]
      with r hr hlowr hqr hsr hAr hwr hVwr hVvr
    have hp : inner ℂ ψ (circleSobolevCoordinate S 4 0 (f r)) = 0 := by
      exact (congrArg (fun z : CircleL2 S => inner ℂ ψ z) hqr.symm).trans (hphase r)
    have hdd : d r = circleSobolevCoordinate S 4 2 (f r) := by
      have hh := congrArg (circleSobolevCoordinate S 2 2) hlowr
      simpa only [circle_sobolev_inclusion_coordinate,circle_sobolev_coordinate_apply] using! hh
    have hb := hpoint (f r) hp hsr
    change A r = circleSobolevPrincipalOperator S (f r) at hAr
    change w r = circleSobolevCoordinate S 4 0 (f r) at hwr
    change Vw r = V (w r) at hVwr
    change Vv r = V (v r) at hVvr
    change q r = circleSobolevCoordinate S 4 0 (f r) at hqr
    change v r = circleNormalGraphModulatedFlow S K (15/2) ψ (f r) at hr
    change e r ≤ -μ*E r-c*‖f r‖^2
    simpa only [e,E,hAr,hVwr,hVvr,hwr,hqr,hdd,hr] using hb
  have hDint : Integrable (fun r : unitInterval => ‖f r‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hscaled : ∀ᵐ r ∂volume,
      (2*τ)*e r ≤ -(2*τ*μ)*E r-(2*τ*c)*‖f r‖^2 := by
    filter_upwards [hpointAE] with r hr
    exact scale_energy_bound (by positivity : 0 ≤ 2*τ) hr
  have hprimitive : ∀ t, E t-E 0 = ∫ r in Iic t, (2*τ)*e r ∂volume := by
    intro t
    rw [integral_const_mul]
    exact henergy t
  have hdecay := unit_interval_energy_decay E (fun r => (2*τ)*e r)
    (fun r => ‖f r‖^2) (2*τ*μ) (2*τ*c) (by positivity) (by positivity)
    (fun r => by dsimp only [E]; positivity) (fun _ => sq_nonneg _)
    (hinte.const_mul (2*τ)) hDint hprimitive hscaled
  refine ⟨hphase,?_⟩
  intro t
  simpa only [neg_mul] using hdecay t

private theorem discard_auxiliary_radius {A B : Type*}
    {p r : A → Prop} {q : B → Prop} {s : A → B → Prop}
    (h : ∃ a, p a ∧ ∃ b, q b ∧ r a ∧ s a b) :
    ∃ a, p a ∧ r a := by
  obtain ⟨a,ha,b,_,hr,_⟩ := h
  exact ⟨a,ha,hr⟩

private theorem energy_radius_data_transport
    {P R : ℝ → Prop} {C : ℝ → ℝ → ℝ → Prop} {Z : Prop}
    (hP : ∃ d > 0, P d) (hR : ∃ r > 0, R r)
    (hC : ∃ κ > 0, ∃ d > 0, ∃ c > 0, C κ d c)
    (k : ∀ d, 0 < d → P d → ∀ r, 0 < r → R r →
      ∀ κ, 0 < κ → ∀ d₁, 0 < d₁ → ∀ c, 0 < c → C κ d₁ c → Z) : Z := by
  obtain ⟨d,hd,hp⟩ := hP
  obtain ⟨r,hr,hrp⟩ := hR
  obtain ⟨κ,hκ,d₁,hd₁,c,hc,hcp⟩ := hC
  exact k d hd hp r hr hrp κ hκ d₁ hd₁ c hc hcp

set_option maxHeartbeats 1000000 in
private theorem parabolic_energy_of_data
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Ψ : CircleL2 S)
    (V : CircleL2 S →L[ℂ] CircleL2 S) (g : ℝ)
    (hphase : ∃ δ₀ > 0, ∀ f : CircleSobolevSpace S 4,
      ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖ < δ₀ →
      circleNormalGraphRotationFunctional S Ψ
        (circleNormalGraphModulatedFlow S K (15/2) Ψ f) = 0)
    (hrotation : ∀ᶠ h : CircleSobolevSpace S 2 in 𝓝 0,
      circleNormalGraphRotationFunctional S Ψ (circleNormalGraphRotationField S K h) ≠ 0)
    (hcombined : ∀ μ : ℝ, 0 < μ → μ < g →
      ∃ κ > 0, ∃ δ₁ > 0, ∃ c > 0, ∀ f : CircleSobolevSpace S 4,
        inner ℂ Ψ (circleSobolevCoordinate S 4 0 f) = 0 →
        ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖ < δ₁ →
        (inner ℂ (circleSobolevPrincipalOperator S f)
          (circleNormalGraphModulatedFlow S K (15/2) Ψ f)).re+
          κ*(inner ℂ (V (circleSobolevCoordinate S 4 0 f))
            (V (circleNormalGraphModulatedFlow S K (15/2) Ψ f))).re ≤
          -μ*(‖circleSobolevCoordinate S 4 0 f‖^2+
            4*‖circleSobolevCoordinate S 4 2 f‖^2+
            κ*‖V (circleSobolevCoordinate S 4 0 f)‖^2)-c*‖f‖^2) :
    ∀ μ : ℝ, 0 < μ → μ < g →
      ∃ κ > 0, ∃ δ > 0, ∃ c > 0,
        (∀ h : CircleSobolevSpace S 2, ‖h‖ < δ →
          circleNormalGraphRotationFunctional S Ψ (circleNormalGraphRotationField S K h) ≠ 0) ∧
        ∀ τ : ℝ, 0 < τ → ∀ U : CircleParabolicSpace S τ,
          inner ℂ Ψ (circleSobolevCoordinate S 2 0 (circleParabolicInitialValue S τ U)) = 0 →
          ‖circleParabolicCurve S τ U‖ < δ →
          (∀ᵐ r : unitInterval ∂volume,
            circleParabolicTimeDerivative S τ U r =
              circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ U r)) →
          let E : unitInterval → ℝ := fun r =>
            ‖circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r)‖^2+
              4*‖circleSobolevCoordinate S 2 2 (circleParabolicCurve S τ U r)‖^2+
              κ*‖V (circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r))‖^2
          (∀ r : unitInterval,
            inner ℂ Ψ (circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r)) = 0) ∧
            ∀ t : unitInterval, E t ≤ Real.exp (-2*τ*μ*(t:ℝ))*E 0 ∧
              (2*τ*c)*(∫ r in Iic t, ‖circleParabolicH4 S τ U r‖^2 ∂volume) ≤ E 0 := by
  intro μ hμ hμg
  refine energy_radius_data_transport hphase (Metric.mem_nhds_iff.mp hrotation)
    (hcombined μ hμ hμg) ?_
  intro δ₀ hδ₀ hphasezero r hrpos hrotball κ hκ δ₁ hδ₁ c hc hpoint
  let δ := min δ₁ (min δ₀ r)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₀ hrpos)
  have hδ₁le : δ ≤ δ₁ := min_le_left _ _
  have hδ₀le : δ ≤ δ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ r := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨κ,hκ,δ,hδ,c,hc,?_,?_⟩
  · intro h hh
    have hb : h ∈ Metric.ball (0 : CircleSobolevSpace S 2) r := by
      simpa only [Metric.mem_ball,dist_zero_right] using hh.trans_le hδr
    exact hrotball hb
  · intro τ hτ U hinit hsmall hPDE
    exact parabolic_modulated_decay S K Ψ V κ δ μ c hκ hδ hμ hc
      (fun f hf => hphasezero f (hf.trans_le hδ₀le))
      (fun f hp hf => hpoint f hp (hf.trans_le hδ₁le))
      τ hτ U hinit hsmall hPDE

end Parabolic

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

set_option maxHeartbeats 1000000 in
/-- Small actual modulated solutions preserve the adjoint phase and decay
at every rate below the proved cover gap, with integrated H4 dissipation. -/
theorem bernoulli_cover_parabolic_energy_estimate
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) :
    let Ext := circlePeriodicExtension T S M hS
    let Q := Ext q
    let P := Ext p
    let K := circleBernoulliBackground S Q P
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    let V : CircleL2 S →L[ℂ] CircleL2 S :=
      (circleCoverStableMetric T S q p hq hp he hqreal hpreal hs hc ho hr
      M hM (ψ:CircleL2 T) hnorm).toContinuousLinearMap
    let gM : ℝ := if M = 1 then 21/4 else 1/(2*(M:ℝ)^2)
    ∀ μ : ℝ, 0 < μ → μ < gM →
      ∃ κ > 0, ∃ δ > 0, ∃ c > 0,
        (∀ h : CircleSobolevSpace S 2, ‖h‖ < δ →
          circleNormalGraphRotationFunctional S (Ψ:CircleL2 S)
            (circleNormalGraphRotationField S K h) ≠ 0) ∧
        ∀ τ : ℝ, 0 < τ → ∀ U : CircleParabolicSpace S τ,
          inner ℂ (Ψ:CircleL2 S)
            (circleSobolevCoordinate S 2 0 (circleParabolicInitialValue S τ U)) = 0 →
          ‖circleParabolicCurve S τ U‖ < δ →
          (∀ᵐ r : unitInterval ∂volume,
            circleParabolicTimeDerivative S τ U r =
              circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S)
                (circleParabolicH4 S τ U r)) →
          let E : unitInterval → ℝ := fun r =>
            ‖circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r)‖^2+
              4*‖circleSobolevCoordinate S 2 2 (circleParabolicCurve S τ U r)‖^2+
              κ*‖V (circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r))‖^2
          (∀ r : unitInterval,
            inner ℂ (Ψ:CircleL2 S)
              (circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U r)) = 0) ∧
            ∀ t : unitInterval, E t ≤ Real.exp (-2*τ*μ*(t:ℝ))*E 0 ∧
              (2*τ*c)*(∫ r in Iic t, ‖circleParabolicH4 S τ U r‖^2 ∂volume) ≤ E 0 := by
  dsimp only
  let Ext := circlePeriodicExtension T S M hS
  let Q := Ext q
  let P := Ext p
  let K := circleBernoulliBackground S Q P
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let V : CircleL2 S →L[ℂ] CircleL2 S :=
      (circleCoverStableMetric T S q p hq hp he hqreal hpreal hs hc ho hr
    M hM (ψ:CircleL2 T) hnorm).toContinuousLinearMap
  have hdata := (paper_periodic_cover_modulated_tame_data T S q p hq hp he
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS).2.2
  have hpair := hdata.2.1
  have hphase := discard_auxiliary_radius hdata.2.2.2.2.2
  have hrotation := ((circle_normal_graph_rotation_normalization S K (Ψ:CircleL2 S)
    hpair).2.2.2.2).mono (fun _ h => h.2.1)
  have hcombined :=
    bernoulli_cover_combined_energy_estimate T S q p hq hp he hqreal hpreal hs hc ho hr
      ψ hnorm hψzero M hM hS
  dsimp only at hcombined
  exact parabolic_energy_of_data S K (Ψ:CircleL2 S) V
    (if M = 1 then 21/4 else 1/(2*(M:ℝ)^2)) hphase hrotation hcombined

end Profile
end Lemniscate
