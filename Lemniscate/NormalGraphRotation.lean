import Lemniscate.NormalGraphLowSobolevCoordinates
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! The rotation field and its adjoint normalization on the H2 graph space.

The physical derivative is supplied by the actual low Sobolev coordinates.
The normalization uses an arbitrary adjoint test vector psi with nonzero
pairing against the reference rotation field. This analytic construction
does not assert a rotation-modulated PDE or uniqueness of its solutions.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

def circleNormalGraphRotationField (K : BackgroundJetOver C(AddCircle T, ℂ))
    (h : CircleSobolevSpace T 2) : CircleL2 T :=
  let z := circleNormalGraphLowCoordinates T h;
  circleContinuousL2 T
    (K.b+(K.eta+z 0)*z 1*Ring.inverse (1-K.k*z 0))

def circleNormalGraphRotationFunctional (ψ : CircleL2 T) : CircleL2 T →L[ℂ] ℂ :=
  innerSL ℂ ψ

def circleNormalGraphNormalizedRotation (K : BackgroundJetOver C(AddCircle T, ℂ))
    (ψ : CircleL2 T) (h : CircleSobolevSpace T 2) : CircleL2 T :=
  (circleNormalGraphRotationFunctional T ψ (circleNormalGraphRotationField T K h))⁻¹ •
    circleNormalGraphRotationField T K h

theorem circle_normal_graph_rotation_normalization
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (ψ : CircleL2 T)
    (hpair : inner ℂ ψ (circleContinuousL2 T K.b) ≠ 0) :
    let b := circleContinuousL2 T K.b
    circleNormalGraphRotationField T K 0 = b ∧
      ContDiffAt ℂ (⊤ : WithTop ℕ∞) (circleNormalGraphRotationField T K) 0 ∧
      ContDiffAt ℂ (⊤ : WithTop ℕ∞) (circleNormalGraphNormalizedRotation T K ψ) 0 ∧
      circleNormalGraphNormalizedRotation T K ψ 0 = (inner ℂ ψ b)⁻¹ • b ∧
      ∀ᶠ h : CircleSobolevSpace T 2 in 𝓝 0,
        circleNormalGraphLowCoordinates T h ∈ normalGraphLowerCoefficientDomain T K ∧
        circleNormalGraphRotationFunctional T ψ (circleNormalGraphRotationField T K h) ≠ 0 ∧
        circleNormalGraphRotationFunctional T ψ (circleNormalGraphNormalizedRotation T K ψ h) = 1 := by
  obtain ⟨hopen,hzero,_⟩ := normal_graph_lower_coefficients_smooth_over C(AddCircle T, ℂ) K 0
  have hu0 : circleNormalGraphLowCoordinates T (0 : CircleSobolevSpace T 2) ∈
      normalGraphLowerCoefficientDomain T K := by
    simpa only [map_zero, normalGraphLowerCoefficientDomain] using hzero
  have hunit : IsUnit (1-K.k*(circleNormalGraphLowCoordinates T
      (0 : CircleSobolevSpace T 2) 0)) := hu0.1
  have h₀ : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun h : CircleSobolevSpace T 2 => circleNormalGraphLowCoordinates T h 0) :=
    ((ContinuousLinearMap.proj (0 : Fin 2)).comp (circleNormalGraphLowCoordinates T)).contDiff
  have h₁ : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun h : CircleSobolevSpace T 2 => circleNormalGraphLowCoordinates T h 1) :=
    ((ContinuousLinearMap.proj (1 : Fin 2)).comp (circleNormalGraphLowCoordinates T)).contDiff
  have hA : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun h : CircleSobolevSpace T 2 => 1-K.k*(circleNormalGraphLowCoordinates T h 0)) := by
    fun_prop
  have hAi : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun h : CircleSobolevSpace T 2 =>
        Ring.inverse (1-K.k*(circleNormalGraphLowCoordinates T h 0))) 0 := by
    have hi := contDiffAt_ringInverse ℂ (n := (⊤ : WithTop ℕ∞)) hunit.unit
    rw [hunit.unit_spec] at hi
    exact hi.comp 0 hA.contDiffAt
  have hC : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun h : CircleSobolevSpace T 2 =>
        K.b+(K.eta+circleNormalGraphLowCoordinates T h 0)*
          circleNormalGraphLowCoordinates T h 1*
          Ring.inverse (1-K.k*(circleNormalGraphLowCoordinates T h 0))) 0 := by
    have h₀at := h₀.contDiffAt (x := (0 : CircleSobolevSpace T 2))
    have h₁at := h₁.contDiffAt (x := (0 : CircleSobolevSpace T 2))
    fun_prop
  have hG : ContDiffAt ℂ (⊤ : WithTop ℕ∞) (circleNormalGraphRotationField T K) 0 := by
    change ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun h : CircleSobolevSpace T 2 => circleContinuousL2 T
        (K.b+(K.eta+circleNormalGraphLowCoordinates T h 0)*
          circleNormalGraphLowCoordinates T h 1*
          Ring.inverse (1-K.k*(circleNormalGraphLowCoordinates T h 0)))) 0
    exact (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).contDiff.contDiffAt.comp 0 hC
  have hG0 : circleNormalGraphRotationField T K 0 = circleContinuousL2 T K.b := by
    simp only [circleNormalGraphRotationField,map_zero,Pi.zero_apply,
      mul_zero,zero_mul,add_zero]
  have hden : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun h : CircleSobolevSpace T 2 =>
        circleNormalGraphRotationFunctional T ψ (circleNormalGraphRotationField T K h)) 0 :=
    (circleNormalGraphRotationFunctional T ψ).contDiff.contDiffAt.comp 0 hG
  have hden0 : circleNormalGraphRotationFunctional T ψ
      (circleNormalGraphRotationField T K 0) ≠ 0 := by
    simpa only [hG0,circleNormalGraphRotationFunctional,innerSL_apply_apply] using hpair
  have hZ : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (circleNormalGraphNormalizedRotation T K ψ) 0 := by
    change ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (fun h : CircleSobolevSpace T 2 =>
        (circleNormalGraphRotationFunctional T ψ (circleNormalGraphRotationField T K h))⁻¹ •
          circleNormalGraphRotationField T K h) 0
    exact (hden.inv hden0).smul hG
  have hZ0 : circleNormalGraphNormalizedRotation T K ψ 0 =
      (inner ℂ ψ (circleContinuousL2 T K.b))⁻¹ • circleContinuousL2 T K.b := by
    simp only [circleNormalGraphNormalizedRotation,hG0,
      circleNormalGraphRotationFunctional,innerSL_apply_apply]
  have htend : Tendsto (circleNormalGraphLowCoordinates T)
      (𝓝 (0 : CircleSobolevSpace T 2)) (𝓝 0) := by
    simpa only [map_zero] using
      ((circleNormalGraphLowCoordinates T).continuous.continuousAt
        (x := (0 : CircleSobolevSpace T 2))).tendsto
  have hdomain : ∀ᶠ h : CircleSobolevSpace T 2 in 𝓝 0,
      circleNormalGraphLowCoordinates T h ∈ normalGraphLowerCoefficientDomain T K :=
    htend.eventually (hopen.mem_nhds hzero)
  have hne : ∀ᶠ h : CircleSobolevSpace T 2 in 𝓝 0,
      circleNormalGraphRotationFunctional T ψ (circleNormalGraphRotationField T K h) ≠ 0 :=
    hden.continuousAt.eventually_ne hden0
  refine ⟨hG0,hG,hZ,hZ0,?_⟩
  filter_upwards [hdomain,hne] with h hd hn
  refine ⟨hd,hn,?_⟩
  change circleNormalGraphRotationFunctional T ψ
    ((circleNormalGraphRotationFunctional T ψ (circleNormalGraphRotationField T K h))⁻¹ •
      circleNormalGraphRotationField T K h) = 1
  rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hn]

end Lemniscate
