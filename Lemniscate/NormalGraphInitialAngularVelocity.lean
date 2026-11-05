import Lemniscate.NormalGraphGlobalAngularVelocity

/-! The continuous initial angular velocity is supplied by the actual
closed-time H5 representative, including its value at the initial endpoint. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate

private theorem initial_angle_norm_radius
    {E : Type*} [NormedAddCommGroup E] (P : E → Prop)
    (h : ∀ᶠ x in 𝓝 (0:E), P x) : ∃ r>0, ∀ x:E, ‖x‖<r → P x := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp h
  exact ⟨r,hr,fun x hx => hball (by simpa only [Metric.mem_ball,dist_zero_right] using hx)⟩

private theorem initial_angle_radius {P : ℝ → Prop} {Q : Prop}
    (h : ∃ r>0, P r) (k : ∀ r, 0<r → P r → Q) : Q := by
  obtain ⟨r,hr,hP⟩ := h
  exact k r hr hP

private theorem initial_angle_continuity_radius {P : ℝ → Prop} {Q : Prop}
    (r₀ : ℝ) (h : ∃ r>0, r≤r₀ ∧ P r)
    (k : ∀ r, 0<r → r≤r₀ → P r → Q) : Q := by
  obtain ⟨r,hr,hr₀,hP⟩ := h
  exact k r hr hr₀ hP

variable (T : ℝ) [Fact (0<T)]

set_option maxHeartbeats 800000 in
/-- The actual angular velocity has a continuous real representative
through the initial endpoint whenever the first H5 lift is continuous.
Only the low H2 norm must be small. -/
theorem circle_initial_normal_graph_angular_velocity
    (K : BackgroundJetOver C(AddCircle T,ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (hpair : inner ℂ ψ (circleContinuousL2 T K.b)≠0)
    (hK : (⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩ :
      BackgroundJetOver C(AddCircle T,ℂ))=K)
    (hψ : circleConjugate T ψ=ψ) :
    ∃ δ>0, ∀ τ : ℝ, ∀ U : CircleParabolicSpace T τ,
      ‖circleParabolicCurve T τ U‖<δ →
      ∀ W : C(unitInterval,CircleSobolevSpace T 5),
      (∀ r : unitInterval, circleSobolevInclusion T 2
        (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 (W r)))=
          circleParabolicCurve T τ U r) →
      (∀ r : unitInterval, circleSobolevConjugation T 2 (circleParabolicCurve T τ U r)=
        circleParabolicCurve T τ U r) →
      ∃ Ω : C(unitInterval,ℝ), ∀ r : unitInterval,
        (Ω r:ℂ)=circleNormalGraphAngularVelocity T K c ψ (circleSobolevInclusion T 4 (W r)) := by
  let N := circleNormalGraphAngularVelocity T K c ψ
  let G := circleNormalGraphRotationField T K
  let ell := circleNormalGraphRotationFunctional T ψ
  have hevent : ∀ᶠ h : CircleSobolevSpace T 2 in 𝓝 0, ell (G h)≠0 :=
    (circle_normal_graph_rotation_normalization T K ψ hpair).2.2.2.2.mono (fun _ hh => hh.2.1)
  refine initial_angle_radius (initial_angle_norm_radius (fun h => ell (G h)≠0) hevent) ?_
  intro δ₀ hδ₀ hden
  refine initial_angle_continuity_radius δ₀
    (angular_velocity_continuous_near_zero T K c ψ hpair δ₀ hδ₀
      (fun f hf => hden _ hf)) ?_
  intro δ hδ _ hcont
  refine ⟨δ,hδ,?_⟩
  intro τ U hU W hW hreal
  let V : unitInterval → CircleSobolevSpace T 4 := fun r => circleSobolevInclusion T 4 (W r)
  have hv : Continuous V := (circleSobolevInclusion T 4).continuous.comp W.continuous
  have hsmall (r : unitInterval) :
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (V r))‖<δ :=
    (congrArg (fun z : CircleSobolevSpace T 2 => ‖z‖) (hW r)).trans_lt
      (((circleParabolicCurve T τ U).norm_coe_le_norm r).trans_lt hU)
  have hn : Continuous (fun r : unitInterval => N (V r)) := by
    simpa only [N,Function.comp_def] using hcont.comp_continuous hv hsmall
  let Ω : C(unitInterval,ℝ) := ⟨fun r => (N (V r)).re,Complex.continuous_re.comp hn⟩
  refine ⟨Ω,?_⟩
  intro r
  have hr := circle_sobolev_h4_real_of_h2 T (V r) _ (hW r) (hreal r)
  have heq := Complex.conj_eq_iff_re.mp
    (circle_normal_graph_angular_velocity_real T K c ψ (V r) hK hψ hr)
  exact heq

end Lemniscate
