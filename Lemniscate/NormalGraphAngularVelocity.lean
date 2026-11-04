import Lemniscate.NormalGraphModulation
import Lemniscate.NormalGraphModulationConjugation

/-! The rotation angular velocity required to reconstruct the unmodulated
normal-graph equation. Its numerator has no linear part, and its denominator
stays nonzero near the reference curve. Only the mixed H2-H4 estimate is used.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

/-- Rotation angular velocity in the adjoint phase condition. -/
def circleNormalGraphAngularVelocity
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (f : CircleSobolevSpace T 4) : ℂ :=
  circleNormalGraphRotationFunctional T ψ (circleNormalGraphFlow T K c f)/
    circleNormalGraphRotationFunctional T ψ
      (circleNormalGraphRotationField T K
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)))

/-- The actual angular velocity has the mixed H2-H4 product bound on a
genuine H2 neighborhood. The same scalar gives the exact reconstruction
identity for the modulated right-hand side. -/
theorem circle_normal_graph_angular_velocity_bound
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (hpair : inner ℂ ψ (circleContinuousL2 T K.b) ≠ 0)
    (hzero : circleNormalGraphFlow T K c 0 = 0)
    (hneutral : ∀ f : CircleSobolevSpace T 4,
      circleNormalGraphRotationFunctional T ψ (circleNormalGraphDerivative T K c f) = 0) :
    (∀ f : CircleSobolevSpace T 4,
      circleNormalGraphModulatedFlow T K c ψ f = circleNormalGraphFlow T K c f-
        circleNormalGraphAngularVelocity T K c ψ f •
          circleNormalGraphRotationField T K
            (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))) ∧
    ∃ δ > 0, ∃ C > 0, ∀ f : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
      circleNormalGraphRotationFunctional T ψ
          (circleNormalGraphRotationField T K
            (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))) ≠ 0 ∧
        ‖circleNormalGraphAngularVelocity T K c ψ f‖ ≤
          C*‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖*‖f‖ := by
  constructor
  · intro f
    simp only [circleNormalGraphModulatedFlow,circleNormalGraphNormalizedRotation,
      circleNormalGraphAngularVelocity,div_eq_mul_inv,smul_smul]
  let F := circleNormalGraphFlow T K c
  let D := circleNormalGraphDerivative T K c
  let ell := circleNormalGraphRotationFunctional T ψ
  let G := circleNormalGraphRotationField T K
  let H : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
    (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
  let d : CircleSobolevSpace T 2 → ℂ := fun h => ell (G h)
  obtain ⟨hGzero,hGsmooth,_,_,_⟩ := circle_normal_graph_rotation_normalization T K ψ hpair
  have hdcont : ContinuousAt d 0 := ell.continuous.continuousAt.comp hGsmooth.continuousAt
  have hd0 : d 0 ≠ 0 := by
    change inner ℂ ψ (circleNormalGraphRotationField T K 0) ≠ 0
    rw [hGzero]
    exact hpair
  let M : ℝ := ‖(d 0)⁻¹‖+1
  have hM : 0 < M := by dsimp only [M]; positivity
  have hdinv : ContinuousAt (fun h => ‖(d h)⁻¹‖) 0 := (hdcont.inv₀ hd0).norm
  have hbound : ∀ᶠ h : CircleSobolevSpace T 2 in 𝓝 0, ‖(d h)⁻¹‖ < M :=
    hdinv.eventually_lt continuousAt_const (by dsimp only [M]; linarith)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((hdcont.eventually_ne hd0).and hbound)
  obtain ⟨rN,hrN,CN,hCN,htame⟩ := circle_normal_graph_sobolev_tame_remainder T K c
  let δ : ℝ := min rN r
  let C : ℝ := 2*CN*‖ell‖*M+1
  have hδ : 0 < δ := lt_min hrN hr
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨δ,hδ,C,hC,?_⟩
  intro f hf
  have hfN : ‖H f‖ < rN := hf.trans_le (min_le_left _ _)
  have hfr : ‖H f‖ < r := hf.trans_le (min_le_right _ _)
  have hmem : H f ∈ Metric.ball (0 : CircleSobolevSpace T 2) r := by
    simpa only [Metric.mem_ball,dist_zero_right] using hfr
  have hden := hball hmem
  refine ⟨hden.1,?_⟩
  have hres : ‖F f-D f‖ ≤ (2*CN)*‖H f‖*‖f‖ := by
    have h := htame f 0 hfN (by simpa only [map_zero,norm_zero] using hrN)
    simp only [hzero,map_zero,norm_zero,add_zero,sub_zero] at h
    change ‖F f-D f‖ ≤ CN*(‖H f‖*‖f‖+‖f‖*‖H f‖) at h
    exact h.trans_eq (by ring)
  have hnum : ‖ell (F f)‖ ≤ ‖ell‖*((2*CN)*‖H f‖*‖f‖) := by
    have hident : ell (F f) = ell (F f-D f) := by
      rw [map_sub,hneutral,sub_zero]
    rw [hident]
    exact (ell.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hres (norm_nonneg ell))
  change ‖ell (F f)/d (H f)‖ ≤ C*‖H f‖*‖f‖
  calc
    _ = ‖ell (F f)‖*‖(d (H f))⁻¹‖ := by rw [div_eq_mul_inv,norm_mul]
    _ ≤ (‖ell‖*((2*CN)*‖H f‖*‖f‖))*M :=
      mul_le_mul hnum hden.2.le (norm_nonneg _) (by positivity)
    _ = (2*CN*‖ell‖*M)*‖H f‖*‖f‖ := by ring
    _ ≤ C*‖H f‖*‖f‖ := by
      have hc : 2*CN*‖ell‖*M ≤ C := le_add_of_nonneg_right zero_le_one
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
        (mul_nonneg (norm_nonneg (H f)) (norm_nonneg f))

open scoped ComplexConjugate

/-- A real background, adjoint vector and height give a real angular
velocity. This also holds when the total quotient has zero denominator. -/
theorem circle_normal_graph_angular_velocity_real
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (f : CircleSobolevSpace T 4)
    (hK : (⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩ :
      BackgroundJetOver C(AddCircle T, ℂ)) = K)
    (hψ : circleConjugate T ψ = ψ) (hf : circleSobolevConjugation T 4 f = f) :
    conj (circleNormalGraphAngularVelocity T K c ψ f) =
      circleNormalGraphAngularVelocity T K c ψ f := by
  let h := circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)
  have hh : circleSobolevConjugation T 2 h = h := by
    apply circle_sobolev_value_injective T 2
    have hv := congrArg (circleSobolevCoordinate T 4 0) hf
    simpa only [circle_sobolev_conjugation_coordinate] using! hv
  have hF := (circle_normal_graph_flow_conjugation T K c f).1
  rw [hK,hf] at hF
  have hG := modulation_rotation_field_conjugation T K h
  change circleConjugate T (circleNormalGraphRotationField T K h) =
    circleNormalGraphRotationField T
      ⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩
      (circleSobolevConjugation T 2 h) at hG
  rw [hK,hh] at hG
  have hnum : conj (inner ℂ ψ (circleNormalGraphFlow T K c f)) =
      inner ℂ ψ (circleNormalGraphFlow T K c f) :=
    (circle_conjugate_inner T ψ _).symm.trans
      (congrArg₂ (fun u v : CircleL2 T => inner ℂ u v) hψ hF)
  have hden : conj (inner ℂ ψ (circleNormalGraphRotationField T K h)) =
      inner ℂ ψ (circleNormalGraphRotationField T K h) :=
    (circle_conjugate_inner T ψ _).symm.trans
      (congrArg₂ (fun u v : CircleL2 T => inner ℂ u v) hψ hG)
  change conj (inner ℂ ψ (circleNormalGraphFlow T K c f)/
    inner ℂ ψ (circleNormalGraphRotationField T K h)) = _
  rw [map_div₀,hnum,hden]
  rfl


end Lemniscate
