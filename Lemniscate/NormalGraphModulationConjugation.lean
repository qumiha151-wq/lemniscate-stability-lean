import Lemniscate.NormalGraphModulation
import Lemniscate.NormalGraphSobolevConjugation

/-! Conjugation of the actual rotation-modulated normal-graph equation.
Every inverse is the total algebraic inverse, so this identity requires no
unit or small-ball hypothesis. Real solution preservation is obtained only
after combining it with the separate local uniqueness theorem. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private def modulationBackgroundStar (K : BackgroundJetOver C(AddCircle T, ℂ)) :
    BackgroundJetOver C(AddCircle T, ℂ) :=
  ⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩

private theorem modulation_inclusion_conjugation (m : ℕ)
    (f : CircleSobolevSpace T (m+1)) :
    circleSobolevInclusion T m (circleSobolevConjugation T (m+1) f) =
      circleSobolevConjugation T m (circleSobolevInclusion T m f) := by
  apply circle_sobolev_value_injective T m
  simp only [circle_sobolev_inclusion_coordinate,circle_sobolev_conjugation_coordinate]

private theorem modulation_low_coordinates_conjugation (h : CircleSobolevSpace T 2) :
    circleNormalGraphLowCoordinates T (circleSobolevConjugation T 2 h) =
      fun j => star (circleNormalGraphLowCoordinates T h j) := by
  funext j
  rw [circle_normal_graph_low_coordinates,circle_normal_graph_low_coordinates]
  fin_cases j <;> simp [modulation_inclusion_conjugation,
    circle_sobolev_conjugation_derivative,circle_sobolev_h1_embedding_conjugation,
    star_smul,Complex.star_def,Complex.conj_ofReal]

/-- Conjugating the actual background and height conjugates the geometric
rotation field, without a smallness or unit-domain hypothesis. -/
theorem modulation_rotation_field_conjugation
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (h : CircleSobolevSpace T 2) :
    circleConjugate T (circleNormalGraphRotationField T K h) =
      circleNormalGraphRotationField T
        ⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩
        (circleSobolevConjugation T 2 h) := by
  have hmul (a b : C(AddCircle T, ℂ)) : star (a*b) = star a*star b :=
    (starRingEnd C(AddCircle T, ℂ)).map_mul a b
  simp only [circleNormalGraphRotationField,modulation_low_coordinates_conjugation,
    modulationBackgroundStar]
  rw [← circle_continuous_l2_star]
  congr 1
  simp only [star_add,star_sub,star_one,hmul,← Ring.inverse_star]

private theorem modulation_functional_conjugation (ψ f : CircleL2 T) :
    circleNormalGraphRotationFunctional T (circleConjugate T ψ) (circleConjugate T f) =
      conj (circleNormalGraphRotationFunctional T ψ f) :=
  circle_conjugate_inner T ψ f

private theorem modulation_normalized_rotation_conjugation
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (ψ : CircleL2 T)
    (h : CircleSobolevSpace T 2) :
    circleConjugate T (circleNormalGraphNormalizedRotation T K ψ h) =
      circleNormalGraphNormalizedRotation T (modulationBackgroundStar T K)
        (circleConjugate T ψ) (circleSobolevConjugation T 2 h) := by
  have hG : circleConjugate T (circleNormalGraphRotationField T K h) =
      circleNormalGraphRotationField T (modulationBackgroundStar T K)
        (circleSobolevConjugation T 2 h) :=
    modulation_rotation_field_conjugation T K h
  have hell : circleNormalGraphRotationFunctional T (circleConjugate T ψ)
      (circleNormalGraphRotationField T (modulationBackgroundStar T K)
        (circleSobolevConjugation T 2 h)) =
      conj (circleNormalGraphRotationFunctional T ψ (circleNormalGraphRotationField T K h)) := by
    rw [← hG]
    exact modulation_functional_conjugation T ψ _
  simp only [circleNormalGraphNormalizedRotation,circle_conjugate_smul,map_inv₀]
  rw [hG,hell]

/-- Conjugating the background, adjoint vector and height conjugates the
actual modulated flow, globally and without any regularity-domain hypothesis. -/
theorem circle_normal_graph_modulated_flow_conjugation
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (f : CircleSobolevSpace T 4) :
    let Kstar : BackgroundJetOver C(AddCircle T, ℂ) :=
      ⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩
    circleConjugate T (circleNormalGraphModulatedFlow T K c ψ f) =
      circleNormalGraphModulatedFlow T Kstar c (circleConjugate T ψ)
        (circleSobolevConjugation T 4 f) := by
  let Kstar := modulationBackgroundStar T K
  let fstar := circleSobolevConjugation T 4 f
  let h := circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)
  have hflow : circleConjugate T (circleNormalGraphFlow T K c f) =
      circleNormalGraphFlow T Kstar c fstar :=
    (circle_normal_graph_flow_conjugation T K c f).1
  have hell : circleNormalGraphRotationFunctional T (circleConjugate T ψ)
      (circleNormalGraphFlow T Kstar c fstar) =
      conj (circleNormalGraphRotationFunctional T ψ (circleNormalGraphFlow T K c f)) := by
    rw [← hflow]
    exact modulation_functional_conjugation T ψ _
  have hinc : circleSobolevInclusion T 2 (circleSobolevInclusion T 3 fstar) =
      circleSobolevConjugation T 2 h := by
    dsimp only [fstar,h]
    rw [modulation_inclusion_conjugation T 3,modulation_inclusion_conjugation T 2]
  change circleConjugate T
      (circleNormalGraphFlow T K c f-
        circleNormalGraphRotationFunctional T ψ (circleNormalGraphFlow T K c f) •
          circleNormalGraphNormalizedRotation T K ψ h) =
    circleNormalGraphFlow T Kstar c fstar-
      circleNormalGraphRotationFunctional T (circleConjugate T ψ)
          (circleNormalGraphFlow T Kstar c fstar) •
        circleNormalGraphNormalizedRotation T Kstar (circleConjugate T ψ)
          (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 fstar))
  rw [circle_conjugate_sub,circle_conjugate_smul,hflow,
    modulation_normalized_rotation_conjugation T K ψ h,hell,hinc]

end Lemniscate
