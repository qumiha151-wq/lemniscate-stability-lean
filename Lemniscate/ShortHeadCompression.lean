import Lemniscate.ShortHeadTransforms

/-! Exact finite compression of the actual transformed operator, without
assuming that the differential operator preserves the finite subspace. -/
namespace Lemniscate
open Complex MeasureTheory Matrix
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleShortHeadCoordinates (f : CircleL2 T) : Fin 15 → ℂ :=
  fun i => fourierCoeff f (shortHeadFrequency i)

noncomputable def circleShortHeadMatrix (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) :
    Matrix (Fin 15) (Fin 15) ℂ := fun i j =>
  inner ℂ (fourierBasis (T := T) (shortHeadFrequency i))
    (A (circleFourierH4 T (shortHeadFrequency j)))

theorem circle_short_head_matrix_mulVec (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (v : Fin 15 → ℂ) :
    circleShortHeadCoordinates T (A (circleShortHead T v)) = circleShortHeadMatrix T A *ᵥ v := by
  funext i
  rw [circleShortHeadCoordinates, ← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  simp only [circleShortHead, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, inner_sum, inner_smul_right,
    circleShortHeadMatrix, mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem circle_short_head_coordinates_householder (e a : Fin 15 → ℂ) (f : CircleL2 T) :
    circleShortHeadCoordinates T
      (neutralHouseholder (circleShortHead T e : CircleL2 T)
        (circleShortHead T a : CircleL2 T) f) =
      shortHeadHouseholderMatrix e a *ᵥ circleShortHeadCoordinates T f := by
  let S := circleShortHead T
  have hsum : (circleShortHead T e : CircleL2 T)+(circleShortHead T a : CircleL2 T) =
      (circleShortHead T (e+a) : CircleL2 T) := by
    exact congrArg (fun g : circleH4Domain T => (g : CircleL2 T)) (S.map_add e a).symm
  rw [short_head_householder_mulVec]
  funext i
  change fourierCoeff _ (shortHeadFrequency i) =
    fourierCoeff f (shortHeadFrequency i)-
      ((1+shortHeadPair e a)⁻¹*shortHeadPair (e+a) (circleShortHeadCoordinates T f))*(e+a) i
  rw [neutral_householder_apply, circle_fourierCoeff_sub, circle_fourierCoeff_smul,
    hsum, circle_short_head_fourier_at, circle_short_head_inner, circle_short_head_pairing]
  rfl

theorem circle_short_head_coordinates_neutral (e p : Fin 15 → ℂ) (f : CircleL2 T) :
    circleShortHeadCoordinates T
      (neutralTransform (circleShortHead T e) (circleShortHead T p : CircleL2 T) f) =
      shortHeadNeutralMatrix e p *ᵥ circleShortHeadCoordinates T f := by
  let S := circleShortHead T
  have hsub : (circleShortHead T p : CircleL2 T)-(circleShortHead T e : CircleL2 T) =
      (circleShortHead T (p-e) : CircleL2 T) := by
    exact congrArg (fun g : circleH4Domain T => (g : CircleL2 T)) (S.map_sub p e).symm
  rw [short_head_neutral_mulVec]
  funext i
  change fourierCoeff _ (shortHeadFrequency i) =
    fourierCoeff f (shortHeadFrequency i)+shortHeadPair (p-e) (circleShortHeadCoordinates T f)*e i
  rw [neutral_transform_apply, circle_fourierCoeff_add, circle_fourierCoeff_smul,
    hsub, circle_short_head_pairing, circle_short_head_fourier_at]
  rfl

theorem circle_short_head_transformed_coordinates (e p a v : Fin 15 → ℂ)
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) :
    circleShortHeadCoordinates T
      (neutralHouseholder (circleShortHead T e : CircleL2 T) (circleShortHead T a : CircleL2 T)
        (neutralTransform (circleShortHead T e) (circleShortHead T p : CircleL2 T)
          (A (neutralTransformInvDomain (circleShortHead T e) (circleShortHead T p : CircleL2 T)
            (neutralHouseholderDomain (circleShortHead T e) (circleShortHead T a)
              (circleShortHead T v)))))) =
      (shortHeadHouseholderMatrix e a*shortHeadNeutralMatrix e p*circleShortHeadMatrix T A*
        shortHeadNeutralInvMatrix e p*shortHeadHouseholderMatrix e a) *ᵥ v := by
  rw [circle_short_head_householder, circle_short_head_neutral_inv,
    circle_short_head_coordinates_householder, circle_short_head_coordinates_neutral,
    circle_short_head_matrix_mulVec]
  simp only [mulVec_mulVec, mul_assoc]

theorem circle_short_head_transformed_pairing (e p a v w : Fin 15 → ℂ)
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) :
    inner ℂ (circleShortHead T v : CircleL2 T)
      (neutralHouseholder (circleShortHead T e : CircleL2 T) (circleShortHead T a : CircleL2 T)
        (neutralTransform (circleShortHead T e) (circleShortHead T p : CircleL2 T)
          (A (neutralTransformInvDomain (circleShortHead T e) (circleShortHead T p : CircleL2 T)
            (neutralHouseholderDomain (circleShortHead T e) (circleShortHead T a)
              (circleShortHead T w)))))) =
      shortHeadPair v ((shortHeadHouseholderMatrix e a*shortHeadNeutralMatrix e p*circleShortHeadMatrix T A*
        shortHeadNeutralInvMatrix e p*shortHeadHouseholderMatrix e a) *ᵥ w) := by
  rw [circle_short_head_pairing]
  change shortHeadPair v (circleShortHeadCoordinates T _) = _
  rw [circle_short_head_transformed_coordinates]

end Lemniscate
