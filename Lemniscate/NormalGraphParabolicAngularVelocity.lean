import Lemniscate.NormalGraphAngularVelocity
import Lemniscate.PeriodicParabolicEstimates
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! The actual angular velocity of a parabolic normal graph is a scalar
time-L2 function. No continuity of the H4 representative in time is used.
Its exact reconstruction identity gives the unmodulated equation.
 -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

private theorem scalar_comp_memLp
    {H : Type*} [NormedAddCommGroup H]
    (s : Set H) (hs : IsOpen s) (h₀ : (0 : H) ∈ s) (N : H → ℂ)
    (hN : ContinuousOn N s) (w : Lp H 2 (volume : Measure unitInterval))
    (hmem : ∀ᵐ t ∂volume, w t ∈ s) (A : ℝ)
    (hbound : ∀ᵐ t ∂volume, ‖N (w t)‖ ≤ A*‖w t‖) :
    MemLp (fun t => N (w t)) 2 (volume : Measure unitInterval) := by
  have hmeas : AEStronglyMeasurable (fun t => N (w t)) volume := by
    borelize H
    obtain ⟨g,hg,hgs,hweq⟩ :=
      (Lp.aestronglyMeasurable w).exists_stronglyMeasurable_range_subset
        hs.measurableSet ⟨0,h₀⟩ hmem
    let z : unitInterval → s := fun t => ⟨g t,hgs t⟩
    have hz : StronglyMeasurable z := by
      apply (Embedding.comp_stronglyMeasurable_iff
        (g := ((↑) : s → H)) Topology.IsEmbedding.subtypeVal).mp
      exact hg
    refine ⟨fun t => N (z t).1,hN.domRestrict.comp_stronglyMeasurable hz,?_⟩
    filter_upwards [hweq] with t ht
    exact congrArg N ht
  exact ((Lp.memLp w).norm.const_mul A).mono' hmeas hbound

private theorem angular_data_transport
    {A Z : Prop} {B : ℝ → ℝ → Prop}
    (h : A ∧ ∃ δ > 0, ∃ C > 0, B δ C)
    (k : A → ∀ δ, 0 < δ → ∀ C, 0 < C → B δ C → Z) : Z := by
  obtain ⟨ha,δ,hδ,C,hC,hB⟩ := h
  exact k ha δ hδ C hC hB

private theorem angular_radius_transport
    {A : ℝ → Prop} {Z : Prop} (h : ∃ δ > 0, A δ)
    (k : ∀ δ, 0 < δ → A δ → Z) : Z := by
  obtain ⟨δ,hδ,hA⟩ := h
  exact k δ hδ hA

variable (T : ℝ) [Fact (0 < T)]

theorem angular_velocity_continuous_near_zero
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (hpair : inner ℂ ψ (circleContinuousL2 T K.b) ≠ 0)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hden : ∀ f : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ₀ →
      circleNormalGraphRotationFunctional T ψ
        (circleNormalGraphRotationField T K
          (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))) ≠ 0) :
    ∃ δ > 0, δ ≤ δ₀ ∧ ContinuousOn (circleNormalGraphAngularVelocity T K c ψ)
      {f : CircleSobolevSpace T 4 |
        ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ} := by
  let S : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
    (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
  let G := circleNormalGraphRotationField T K
  let ell := circleNormalGraphRotationFunctional T ψ
  have hG : ContDiffAt ℂ 1 G 0 :=
    (circle_normal_graph_rotation_normalization T K ψ hpair).2.1.of_le le_top
  have hGe : ∀ᶠ h : CircleSobolevSpace T 2 in 𝓝 0, ContinuousAt G h :=
    (hG.eventually (by simp)).mono (fun _ h => h.continuousAt)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hGe
  obtain ⟨d,hd,hflowdomain⟩ := circle_normal_graph_h2_small_domain T K
  let δ := min δ₀ (min d r)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hd hr)
  let D : Set (CircleSobolevSpace T 4) := {f | ‖S f‖ < δ}
  have hGon : ContinuousOn G (Metric.ball (0 : CircleSobolevSpace T 2) r) :=
    fun _ hh => (hball hh).continuousWithinAt
  have hSball : MapsTo S D (Metric.ball (0 : CircleSobolevSpace T 2) r) := by
    intro f hf
    have hfr : ‖S f‖ < r := hf.trans_le ((min_le_right δ₀ (min d r)).trans (min_le_right d r))
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hfr
  have hnum : ContinuousOn (fun f => ell (circleNormalGraphFlow T K c f)) D := by
    intro f hf
    have hfd : ‖S f‖ < d := hf.trans_le ((min_le_right δ₀ (min d r)).trans (min_le_left d r))
    have hF := ((circle_normal_graph_flow_smooth T K c).2.2 f (hflowdomain f hfd)).continuousAt
    exact (ell.continuous.continuousAt.comp hF).continuousWithinAt
  have hdencont : ContinuousOn (fun f => ell (G (S f))) D :=
    ell.continuous.comp_continuousOn (hGon.comp S.continuous.continuousOn hSball)
  refine ⟨δ,hδ,min_le_left _ _,?_⟩
  change ContinuousOn (fun f => ell (circleNormalGraphFlow T K c f)/ell (G (S f))) D
  exact hnum.div hdencont (fun f hf => hden f (hf.trans_le (min_le_left _ _)))

set_option maxHeartbeats 800000 in
/-- On one H2 neighbourhood, every actual parabolic normal graph has a
genuine scalar L2 angular velocity with the mixed H2-H4 bound. A solution
of the modulated equation therefore satisfies the actual unmodulated
equation with this same time-dependent angular velocity. -/
theorem circle_parabolic_normal_graph_angular_velocity
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (hpair : inner ℂ ψ (circleContinuousL2 T K.b) ≠ 0)
    (hFzero : circleNormalGraphFlow T K c 0 = 0)
    (hneutral : ∀ f : CircleSobolevSpace T 4,
      circleNormalGraphRotationFunctional T ψ (circleNormalGraphDerivative T K c f) = 0) :
    ∃ δ > 0, ∃ C > 0, ∀ τ : ℝ, ∀ U : CircleParabolicSpace T τ,
      ‖circleParabolicCurve T τ U‖ < δ →
      ∃ φ : Lp ℂ 2 (volume : Measure unitInterval),
        ((φ : unitInterval → ℂ) =ᵐ[volume]
          fun t => circleNormalGraphAngularVelocity T K c ψ (circleParabolicH4 T τ U t)) ∧
        ‖φ‖ ≤ C*‖circleParabolicCurve T τ U‖*‖circleParabolicH4 T τ U‖ ∧
        ((∀ᵐ t : unitInterval ∂volume, circleParabolicTimeDerivative T τ U t =
            circleNormalGraphModulatedFlow T K c ψ (circleParabolicH4 T τ U t)) →
          ∀ᵐ t : unitInterval ∂volume, circleParabolicTimeDerivative T τ U t =
            circleNormalGraphFlow T K c (circleParabolicH4 T τ U t)-
              φ t • circleNormalGraphRotationField T K (circleParabolicCurve T τ U t)) := by
  refine angular_data_transport
    (circle_normal_graph_angular_velocity_bound T K c ψ hpair hFzero hneutral) ?_
  intro hreconstruct δ₀ hδ₀ C hC hbound
  refine angular_radius_transport
    (angular_velocity_continuous_near_zero T K c ψ hpair δ₀ hδ₀
      (fun f hf => (hbound f hf).1)) ?_
  intro δ hδ hdata
  have hδle := hdata.1
  have hcontinuous := hdata.2
  refine ⟨δ,hδ,C,hC,?_⟩
  intro τ U hU
  let S : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
    (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
  let D : Set (CircleSobolevSpace T 4) := {f | ‖S f‖ < δ}
  let w := circleParabolicH4 T τ U
  let N := circleNormalGraphAngularVelocity T K c ψ
  let A : ℝ := C*‖circleParabolicCurve T τ U‖
  have hinc : ∀ᵐ t ∂volume, circleParabolicCurve T τ U t = S (w t) :=
    circle_parabolic_h2_h4_ae T τ U
  have hnorm : ∀ᵐ t ∂volume, ‖S (w t)‖ ≤ ‖circleParabolicCurve T τ U‖ := by
    filter_upwards [hinc] with t ht
    exact (congrArg (fun x : CircleSobolevSpace T 2 => ‖x‖) ht.symm).le.trans
      ((circleParabolicCurve T τ U).norm_coe_le_norm t)
  have hmem : ∀ᵐ t ∂volume, w t ∈ D := hnorm.mono (fun _ ht => ht.trans_lt hU)
  have hpoint : ∀ᵐ t ∂volume, ‖N (w t)‖ ≤ A*‖w t‖ := by
    filter_upwards [hnorm,hmem] with t hn hm
    exact (hbound (w t) (hm.trans_le hδle)).2.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC.le) (norm_nonneg (w t)))
  have hM : MemLp (fun t => N (w t)) 2 (volume : Measure unitInterval) :=
    scalar_comp_memLp D (isOpen_Iio.preimage S.continuous.norm)
      (by simpa only [D,mem_setOf_eq,map_zero,norm_zero] using hδ)
      N hcontinuous w hmem A hpoint
  let φ : Lp ℂ 2 (volume : Measure unitInterval) := hM.toLp (fun t => N (w t))
  have hφ : (φ : unitInterval → ℂ) =ᵐ[volume] fun t => N (w t) := MemLp.coeFn_toLp hM
  have hφnorm : ‖φ‖ ≤ A*‖w‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hφ,hpoint] with t ht hp
    exact (congrArg (fun z : ℂ => ‖z‖) ht).trans_le hp
  refine ⟨φ,hφ,hφnorm,?_⟩
  intro hPDE
  filter_upwards [hPDE,hφ,hinc] with t hp hφt ht
  have hcorrection : N (w t) • circleNormalGraphRotationField T K (S (w t)) =
      φ t • circleNormalGraphRotationField T K (circleParabolicCurve T τ U t) :=
    congrArg₂ (fun (a : ℂ) (h : CircleSobolevSpace T 2) =>
      a • circleNormalGraphRotationField T K h) hφt.symm ht.symm
  exact hp.trans ((hreconstruct (w t)).trans
    (congrArg (fun z : CircleL2 T => circleNormalGraphFlow T K c (w t)-z) hcorrection))

end Lemniscate
