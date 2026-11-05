import Lemniscate.NormalGraphParabolicAngularVelocity
import Lemniscate.PeriodicParabolicGlobalSolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The angular velocity of the actual global modulated solution.
The first MR segment supplies integrability at the initial endpoint;
positive-time H4 continuity supplies continuity elsewhere. No angular
primitive or limiting angle is assumed or constructed in this module.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate

private theorem unit_interval_positive_ae :
    ∀ᵐ (r : unitInterval) ∂volume, 0 < (r:ℝ) := by
  filter_upwards [(volume : Measure unitInterval).ae_ne 0] with r hr
  have hne : (r:ℝ) ≠ 0 := fun h => hr (Subtype.ext h)
  exact lt_of_le_of_ne r.property.1 (Ne.symm hne)

private theorem local_integrable_of_first_segment
    (ω : ℝ → ℝ) (hzero : ∀ t : ℝ, t ≤ 0 → ω t=0)
    (hcont : ContinuousOn ω (Ioi (0:ℝ)))
    (τ : ℝ) (hτ : 0 < τ) (f : unitInterval → ℝ) (hf : Integrable f volume)
    (heq : ∀ᵐ (r : unitInterval) ∂volume, ω (τ*(r:ℝ))=f r) :
    ∀ a b : ℝ, IntervalIntegrable ω volume a b := by
  have heq' : f =ᵐ[volume] fun r : unitInterval => ω (τ*(r:ℝ)) := by
    filter_upwards [heq] with r hr
    exact hr.symm
  have hi : Integrable (fun r : unitInterval => ω (τ*(r:ℝ))) volume := hf.congr heq'
  have hOn : IntegrableOn (fun r : ℝ => ω (τ*r)) (Icc (0:ℝ) 1) volume := by
    apply (unitInterval.measurePreserving_coe.integrable_comp_emb
      unitInterval.measurableEmbedding_coe).mp
    simpa only [Function.comp_def] using hi
  have h01 : IntervalIntegrable (fun r : ℝ => ω (τ*r)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hOn
  have h0τ : IntervalIntegrable ω volume 0 τ := by
    simpa only [zero_div,one_div,inv_inv,← mul_assoc,mul_inv_cancel₀ (ne_of_gt hτ),
      one_mul] using h01.comp_mul_left (c := τ⁻¹)
  have h0 (b : ℝ) : IntervalIntegrable ω volume 0 b := by
    by_cases hb : b ≤ 0
    · apply IntervalIntegrable.symm
      apply (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume b 0).congr
      intro x hx
      rw [uIoc_of_le hb] at hx
      exact (hzero x hx.2).symm
    · have hbp : 0 < b := lt_of_not_ge hb
      by_cases hbτ : b ≤ τ
      · apply h0τ.mono_set
        rw [uIcc_of_le hbp.le,uIcc_of_le hτ.le]
        exact Icc_subset_Icc le_rfl hbτ
      · apply h0τ.trans
        have hτb : τ ≤ b := (lt_of_not_ge hbτ).le
        have hc : ContinuousOn ω (uIcc τ b) := hcont.mono (by
          rw [uIcc_of_le hτb]
          intro x hx
          exact hτ.trans_le hx.1)
        exact hc.intervalIntegrable
  exact fun a b => (h0 a).symm.trans (h0 b)

private theorem positive_pair_data
    {P : ℝ → ℝ → Prop} {Z : Prop}
    (h : ∃ δ > 0, ∃ C > 0, P δ C)
    (k : ∀ δ, 0 < δ → ∀ C, 0 < C → P δ C → Z) : Z := by
  obtain ⟨δ,hδ,C,hC,hP⟩ := h
  exact k δ hδ C hC hP

private theorem positive_radius_data
    {P : ℝ → Prop} {Z : Prop} {δ₀ : ℝ}
    (h : ∃ δ > 0, δ ≤ δ₀ ∧ P δ)
    (k : ∀ δ, 0 < δ → δ ≤ δ₀ → P δ → Z) : Z := by
  obtain ⟨δ,hδ,hδ₀,hP⟩ := h
  exact k δ hδ hδ₀ hP

private theorem angular_velocity_witness_data
    {X : Type*} {P Q : X → Prop} (h : ∃ x, P x)
    (k : ∀ x, P x → Q x) : ∃ x, Q x := by
  obtain ⟨x,hx⟩ := h
  exact ⟨x,k x hx⟩

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sobolev_h4_real_of_h2
    (f : CircleSobolevSpace T 4) (g : CircleSobolevSpace T 2)
    (hfg : circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)=g)
    (hg : circleSobolevConjugation T 2 g=g) :
    circleSobolevConjugation T 4 f=f := by
  have hv : circleSobolevCoordinate T 4 0 f=circleSobolevCoordinate T 2 0 g :=
    congrArg (circleSobolevCoordinate T 2 0) hfg
  have hr : circleConjugate T (circleSobolevCoordinate T 2 0 g)=
      circleSobolevCoordinate T 2 0 g := by
    simpa only [circle_sobolev_conjugation_coordinate] using
      congrArg (circleSobolevCoordinate T 2 0) hg
  apply circle_sobolev_value_injective T 4
  exact (circle_sobolev_conjugation_coordinate T 4 0 f).trans
    ((congrArg (circleConjugate T) hv).trans (hr.trans hv.symm))

set_option maxHeartbeats 800000 in
/-- The actual global angular velocity is real, continuous at positive
times, agrees with every segment's scalar MR velocity, and is locally
integrable on the real line. Actual H2 and H4 decay gives its exponential
tail, ready for the separate rotation-angle convergence theorem. -/
theorem circle_global_normal_graph_angular_velocity
    (K : BackgroundJetOver C(AddCircle T,ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (hpair : inner ℂ ψ (circleContinuousL2 T K.b) ≠ 0)
    (hFzero : circleNormalGraphFlow T K c 0=0)
    (hneutral : ∀ f : CircleSobolevSpace T 4,
      circleNormalGraphRotationFunctional T ψ (circleNormalGraphDerivative T K c f)=0)
    (hK : (⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩ :
      BackgroundJetOver C(AddCircle T,ℂ))=K)
    (hψ : circleConjugate T ψ=ψ) :
    ∃ δ > 0, ∃ C > 0, ∀ τ : ℝ, ∀ hτ : 0 < τ,
      ∀ u : C(ℝ≥0,CircleSobolevSpace T 2), ∀ U : ℕ → CircleParabolicSpace T τ,
      ∀ w₄ : C(Ioi (0:ℝ),CircleSobolevSpace T 4),
      (∀ n, ‖circleParabolicCurve T τ (U n)‖ < δ) →
      (∀ n r, u (circleParabolicSegmentTime τ hτ n r)=circleParabolicCurve T τ (U n) r) →
      (∀ t : ℝ≥0, 0 < t → ∃ (n : ℕ) (r : unitInterval),
        0 < (r:ℝ) ∧ (r:ℝ) < 1 ∧ circleParabolicSegmentTime τ hτ n r=t) →
      (∀ t : Ioi (0:ℝ), circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (w₄ t))=
        u ⟨(t:ℝ),t.property.le⟩) →
      (∀ t : ℝ≥0, circleSobolevConjugation T 2 (u t)=u t) →
      (∀ n, ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (U n) r=
        circleNormalGraphModulatedFlow T K c ψ (circleParabolicH4 T τ (U n) r)) →
      ∀ t₀ μ A₂ A₄ : ℝ, 0 < t₀ → 0 < μ → 0 ≤ A₂ → 0 ≤ A₄ →
      (∀ t : Ioi (0:ℝ), t₀ ≤ (t:ℝ) →
        ‖u ⟨(t:ℝ),t.property.le⟩‖ ≤ A₂*Real.exp (-μ*(t:ℝ)) ∧
          ‖w₄ t‖ ≤ A₄*Real.exp (-μ*(t:ℝ))) →
      let ω : ℝ → ℝ := fun t => if ht : 0 < t then
        (circleNormalGraphAngularVelocity T K c ψ (w₄ ⟨t,ht⟩)).re else 0
      (∀ t : ℝ, t ≤ 0 → ω t=0) ∧
        (∀ t : Ioi (0:ℝ), (ω (t:ℝ):ℂ)=circleNormalGraphAngularVelocity T K c ψ (w₄ t)) ∧
        ContinuousOn ω (Ioi (0:ℝ)) ∧
        (∀ n, ∃ φ : Lp ℂ 2 (volume : Measure unitInterval),
          ((φ : unitInterval → ℂ) =ᵐ[volume] fun r =>
            circleNormalGraphAngularVelocity T K c ψ (circleParabolicH4 T τ (U n) r)) ∧
          ((φ : unitInterval → ℂ) =ᵐ[volume] fun r =>
            (ω (circleParabolicSegmentTime τ hτ n r):ℂ)) ∧
          ‖φ‖ ≤ C*‖circleParabolicCurve T τ (U n)‖*‖circleParabolicH4 T τ (U n)‖ ∧
          (∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (U n) r=
            circleNormalGraphFlow T K c (circleParabolicH4 T τ (U n) r)-
              φ r • circleNormalGraphRotationField T K (circleParabolicCurve T τ (U n) r))) ∧
        (∀ a b : ℝ, IntervalIntegrable ω volume a b) ∧
        ∀ t : ℝ, t₀ ≤ t → |ω t| ≤ C*A₂*A₄*Real.exp (-(2*μ)*t) := by
  refine positive_pair_data
    (circle_normal_graph_angular_velocity_bound T K c ψ hpair hFzero hneutral).2 ?_
  intro δ₀ hδ₀ C₀ hC₀ hbound
  refine positive_radius_data
    (angular_velocity_continuous_near_zero T K c ψ hpair δ₀ hδ₀
      (fun f hf => (hbound f hf).1)) ?_
  intro δc hδc hδc₀ hcontinuous
  refine positive_pair_data
    (circle_parabolic_normal_graph_angular_velocity T K c ψ hpair hFzero hneutral) ?_
  intro δa hδa Ca hCa hangle
  let δ := min δc δa
  let C := C₀+Ca+1
  have hδ : 0 < δ := lt_min hδc hδa
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC₀le : C₀ ≤ C := by dsimp only [C]; linarith
  have hCale : Ca ≤ C := by dsimp only [C]; linarith
  refine ⟨δ,hδ,C,hC,?_⟩
  intro τ hτ u U w₄ hU hrep hcover hw₄ hreal hPDE t₀ μ A₂ A₄ ht₀ hμ hA₂ hA₄ hdecay
  dsimp only
  let N := circleNormalGraphAngularVelocity T K c ψ
  let ω : ℝ → ℝ := fun t => if ht : 0 < t then (N (w₄ ⟨t,ht⟩)).re else 0
  have hzero (t : ℝ) (ht : t ≤ 0) : ω t=0 := dif_neg (not_lt_of_ge ht)
  have hsmall (t : Ioi (0:ℝ)) : ‖u ⟨(t:ℝ),t.property.le⟩‖ < δ := by
    obtain ⟨n,r,_,_,hr⟩ := hcover ⟨(t:ℝ),t.property.le⟩ t.property
    have hu : u ⟨(t:ℝ),t.property.le⟩=circleParabolicCurve T τ (U n) r :=
      (congrArg u hr.symm).trans (hrep n r)
    exact (congrArg (fun f : CircleSobolevSpace T 2 => ‖f‖) hu).trans_lt
      (((circleParabolicCurve T τ (U n)).norm_coe_le_norm r).trans_lt (hU n))
  have hwsmall (t : Ioi (0:ℝ)) :
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (w₄ t))‖ < δ :=
    (congrArg (fun f : CircleSobolevSpace T 2 => ‖f‖) (hw₄ t)).trans_lt (hsmall t)
  have hωreal (t : Ioi (0:ℝ)) : (ω (t:ℝ):ℂ)=N (w₄ t) := by
    have hwr : circleSobolevConjugation T 4 (w₄ t)=w₄ t :=
      circle_sobolev_h4_real_of_h2 T (w₄ t) _ (hw₄ t) (hreal _)
    have hc := Complex.conj_eq_iff_re.mp
      (circle_normal_graph_angular_velocity_real T K c ψ (w₄ t) hK hψ hwr)
    have hvalue : ω (t:ℝ)=(N (w₄ t)).re := by
      exact dif_pos (show 0<(t:ℝ) from t.property)
    exact (congrArg Complex.ofReal hvalue).trans hc
  have hNcont : Continuous (fun t : Ioi (0:ℝ) => N (w₄ t)) := by
    simpa only [Function.comp_def] using hcontinuous.comp_continuous w₄.continuous
      (fun t => (hwsmall t).trans_le (min_le_left δc δa))
  have hcont : ContinuousOn ω (Ioi (0:ℝ)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun t : Ioi (0:ℝ) => (N (w₄ t)).re) :=
      Complex.continuous_re.comp hNcont
    have heq : (Ioi (0:ℝ)).domRestrict ω=(fun t => (N (w₄ t)).re) := by
      funext t
      exact dif_pos (show 0<(t:ℝ) from t.property)
    exact heq.symm ▸ hc
  have hsegments (n : ℕ) : ∃ φ : Lp ℂ 2 (volume : Measure unitInterval),
      ((φ : unitInterval → ℂ) =ᵐ[volume] fun r => N (circleParabolicH4 T τ (U n) r)) ∧
      ((φ : unitInterval → ℂ) =ᵐ[volume] fun r => (ω (circleParabolicSegmentTime τ hτ n r):ℂ)) ∧
      ‖φ‖ ≤ C*‖circleParabolicCurve T τ (U n)‖*‖circleParabolicH4 T τ (U n)‖ ∧
      (∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (U n) r=
        circleNormalGraphFlow T K c (circleParabolicH4 T τ (U n) r)-
          φ r • circleNormalGraphRotationField T K (circleParabolicCurve T τ (U n) r)) := by
    refine angular_velocity_witness_data (X := Lp ℂ 2 (volume : Measure unitInterval))
      (hangle τ (U n) ((hU n).trans_le (min_le_right δc δa))) ?_
    intro φ hdata
    obtain ⟨hφ,hφnorm,hunmod⟩ := hdata
    refine ⟨hφ,?_,?_,hunmod (hPDE n)⟩
    · filter_upwards [hφ,circle_parabolic_h2_h4_ae T τ (U n),unit_interval_positive_ae]
        with r hφr hMR hr
      have ht : 0 < (circleParabolicSegmentTime τ hτ n r:ℝ) :=
        mul_pos hτ (add_pos_of_nonneg_of_pos (by positivity) hr)
      let t : Ioi (0:ℝ) := ⟨(circleParabolicSegmentTime τ hτ n r:ℝ),ht⟩
      have htNN : (⟨(t:ℝ),t.property.le⟩ : ℝ≥0)=circleParabolicSegmentTime τ hτ n r :=
        Subtype.ext rfl
      have heq : w₄ t=circleParabolicH4 T τ (U n) r := by
        apply circle_sobolev_value_injective T 4
        change circleSobolevCoordinate T 2 0
          (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (w₄ t))) =
            circleSobolevCoordinate T 2 0
              (circleSobolevInclusion T 2
                (circleSobolevInclusion T 3 (circleParabolicH4 T τ (U n) r)))
        exact congrArg (circleSobolevCoordinate T 2 0)
          ((hw₄ t).trans ((congrArg u htNN).trans ((hrep n r).trans hMR)))
      exact hφr.trans ((congrArg N heq.symm).trans (hωreal t).symm)
    · have hH4nonneg : 0≤‖circleParabolicH4 T τ (U n)‖ := by
        change 0≤ENNReal.toReal _
        exact ENNReal.toReal_nonneg
      exact hφnorm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCale
          (norm_nonneg (circleParabolicCurve T τ (U n)))) hH4nonneg)
  have hlocal : ∀ a b : ℝ, IntervalIntegrable ω volume a b := by
    obtain ⟨φ,_,hφω,_,_⟩ := hsegments 0
    have hφint : Integrable (φ : unitInterval → ℂ) volume :=
      memLp_one_iff_integrable.mp ((Lp.memLp φ).mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2))
    have hf : Integrable (fun r : unitInterval => (φ r).re) volume :=
      Complex.reCLM.integrable_comp hφint
    apply local_integrable_of_first_segment ω hzero hcont τ hτ _ hf
    filter_upwards [hφω] with r hr
    have he : ω (circleParabolicSegmentTime τ hτ 0 r)=(φ r).re :=
      (congrArg Complex.re hr).symm
    have htime : (circleParabolicSegmentTime τ hτ 0 r:ℝ)=τ*(r:ℝ) := by
      simp only [circleParabolicSegmentTime,NNReal.coe_mk,Nat.cast_zero,zero_div,zero_add]
      rfl
    exact (congrArg ω htime).symm.trans he
  refine ⟨hzero,hωreal,hcont,hsegments,hlocal,?_⟩
  intro t ht
  let z : Ioi (0:ℝ) := ⟨t,ht₀.trans_le ht⟩
  have hb := (hbound (w₄ z)
    ((hwsmall z).trans_le ((min_le_left δc δa).trans hδc₀))).2
  have hincnorm := congrArg (fun f : CircleSobolevSpace T 2 => ‖f‖) (hw₄ z)
  have hb' : ‖N (w₄ z)‖ ≤ C₀*‖u ⟨(z:ℝ),z.property.le⟩‖*‖w₄ z‖ :=
    hb.trans_eq (congrArg (fun a : ℝ => C₀*a*‖w₄ z‖) hincnorm)
  have hprod := mul_le_mul (hdecay z ht).1 (hdecay z ht).2
    (norm_nonneg (w₄ z)) (mul_nonneg hA₂ (Real.exp_pos _).le)
  have he : Real.exp (-μ*t)*Real.exp (-μ*t)=Real.exp (-(2*μ)*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    |ω t| = ‖(ω t:ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs]
    _ = ‖N (w₄ z)‖ := congrArg (fun a : ℂ => ‖a‖) (hωreal z)
    _ ≤ C₀*‖u ⟨(z:ℝ),z.property.le⟩‖*‖w₄ z‖ := hb'
    _ = C₀*(‖u ⟨(z:ℝ),z.property.le⟩‖*‖w₄ z‖) := by ring
    _ ≤ C*(‖u ⟨(z:ℝ),z.property.le⟩‖*‖w₄ z‖) :=
      mul_le_mul_of_nonneg_right hC₀le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ C*((A₂*Real.exp (-μ*t))*(A₄*Real.exp (-μ*t))) :=
      mul_le_mul_of_nonneg_left hprod hC.le
    _ = C*A₂*A₄*(Real.exp (-μ*t)*Real.exp (-μ*t)) := by ring
    _ = C*A₂*A₄*Real.exp (-(2*μ)*t) := by rw [he]

end Lemniscate
