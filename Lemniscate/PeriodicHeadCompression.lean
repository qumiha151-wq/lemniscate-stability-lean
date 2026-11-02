import Lemniscate.PeriodicHeadTransforms

/-! Exact finite compression of the actual transformed operator, without
assuming that the differential operator preserves the finite subspace. -/
namespace Lemniscate
open Complex MeasureTheory Matrix
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleEvenHeadCoordinates (f : CircleL2 T) : Fin 31 → ℂ :=
  fun i => fourierCoeff f (evenHeadFrequency i)

noncomputable def circleHeadMatrix (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) :
    Matrix (Fin 31) (Fin 31) ℂ := fun i j =>
  inner ℂ (fourierBasis (T := T) (evenHeadFrequency i))
    (A (circleFourierH4 T (evenHeadFrequency j)))

theorem circle_head_matrix_mulVec (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (v : Fin 31 → ℂ) :
    circleEvenHeadCoordinates T (A (circleEvenHeadH4 T v)) = circleHeadMatrix T A *ᵥ v := by
  funext i
  rw [circleEvenHeadCoordinates, ← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  simp only [circleEvenHeadH4, map_sum, map_smul, inner_sum, inner_smul_right,
    circleHeadMatrix, mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem circle_even_head_coordinates_householder (e a : Fin 31 → ℂ) (f : CircleL2 T) :
    circleEvenHeadCoordinates T
      (neutralHouseholder (circleEvenHeadH4 T e : CircleL2 T)
        (circleEvenHeadH4 T a : CircleL2 T) f) =
      headHouseholderMatrix e a *ᵥ circleEvenHeadCoordinates T f := by
  let S := circleEvenHeadLinearMap T
  have hsum : (circleEvenHeadH4 T e : CircleL2 T)+(circleEvenHeadH4 T a : CircleL2 T) =
      (circleEvenHeadH4 T (e+a) : CircleL2 T) := by
    exact congrArg (fun g : circleH4Domain T => (g : CircleL2 T)) (S.map_add e a).symm
  rw [head_householder_mulVec]
  funext i
  change fourierCoeff _ (evenHeadFrequency i) =
    fourierCoeff f (evenHeadFrequency i)-
      ((1+headPair e a)⁻¹*headPair (e+a) (circleEvenHeadCoordinates T f))*(e+a) i
  rw [neutral_householder_apply, circle_fourierCoeff_sub, circle_fourierCoeff_smul,
    hsum, circle_even_head_fourier_at, circle_even_head_inner, circle_even_head_pairing]
  rfl

theorem circle_even_head_coordinates_neutral (e p : Fin 31 → ℂ) (f : CircleL2 T) :
    circleEvenHeadCoordinates T
      (neutralTransform (circleEvenHeadH4 T e) (circleEvenHeadH4 T p : CircleL2 T) f) =
      headNeutralMatrix e p *ᵥ circleEvenHeadCoordinates T f := by
  let S := circleEvenHeadLinearMap T
  have hsub : (circleEvenHeadH4 T p : CircleL2 T)-(circleEvenHeadH4 T e : CircleL2 T) =
      (circleEvenHeadH4 T (p-e) : CircleL2 T) := by
    exact congrArg (fun g : circleH4Domain T => (g : CircleL2 T)) (S.map_sub p e).symm
  rw [head_neutral_mulVec]
  funext i
  change fourierCoeff _ (evenHeadFrequency i) =
    fourierCoeff f (evenHeadFrequency i)+headPair (p-e) (circleEvenHeadCoordinates T f)*e i
  rw [neutral_transform_apply, circle_fourierCoeff_add, circle_fourierCoeff_smul,
    hsub, circle_even_head_pairing, circle_even_head_fourier_at]
  rfl

theorem circle_head_transformed_coordinates (e p a v : Fin 31 → ℂ)
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) :
    circleEvenHeadCoordinates T
      (neutralHouseholder (circleEvenHeadH4 T e : CircleL2 T) (circleEvenHeadH4 T a : CircleL2 T)
        (neutralTransform (circleEvenHeadH4 T e) (circleEvenHeadH4 T p : CircleL2 T)
          (A (neutralTransformInvDomain (circleEvenHeadH4 T e) (circleEvenHeadH4 T p : CircleL2 T)
            (neutralHouseholderDomain (circleEvenHeadH4 T e) (circleEvenHeadH4 T a)
              (circleEvenHeadH4 T v)))))) =
      (headHouseholderMatrix e a*headNeutralMatrix e p*circleHeadMatrix T A*
        headNeutralInvMatrix e p*headHouseholderMatrix e a) *ᵥ v := by
  rw [circle_even_head_householder, circle_even_head_neutral_inv,
    circle_even_head_coordinates_householder, circle_even_head_coordinates_neutral,
    circle_head_matrix_mulVec]
  simp only [mulVec_mulVec, mul_assoc]

theorem circle_head_transformed_pairing (e p a v w : Fin 31 → ℂ)
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) :
    inner ℂ (circleEvenHeadH4 T v : CircleL2 T)
      (neutralHouseholder (circleEvenHeadH4 T e : CircleL2 T) (circleEvenHeadH4 T a : CircleL2 T)
        (neutralTransform (circleEvenHeadH4 T e) (circleEvenHeadH4 T p : CircleL2 T)
          (A (neutralTransformInvDomain (circleEvenHeadH4 T e) (circleEvenHeadH4 T p : CircleL2 T)
            (neutralHouseholderDomain (circleEvenHeadH4 T e) (circleEvenHeadH4 T a)
              (circleEvenHeadH4 T w)))))) =
      headPair v ((headHouseholderMatrix e a*headNeutralMatrix e p*circleHeadMatrix T A*
        headNeutralInvMatrix e p*headHouseholderMatrix e a) *ᵥ w) := by
  rw [circle_even_head_pairing]
  change headPair v (circleEvenHeadCoordinates T _) = _
  rw [circle_head_transformed_coordinates]

end Lemniscate
