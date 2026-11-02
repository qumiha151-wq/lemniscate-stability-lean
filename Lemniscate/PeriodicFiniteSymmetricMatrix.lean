import Lemniscate.PeriodicFiniteMatrixIdentification
import Lemniscate.PeriodicFiniteBlochForm
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! Exact Hermitian coefficient matrices of the finite Bloch form.
The constant term is formed before the approximate neutral conjugation. -/
namespace Lemniscate
open Complex MeasureTheory Matrix
open scoped ComplexConjugate

theorem head_pair_conj_symm (v w : Fin 31 → ℂ) : headPair v w = conj (headPair w v) := by
  simp only [headPair, map_sum, map_mul, conj_conj]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem head_pair_mulVec_left (M : Matrix (Fin 31) (Fin 31) ℂ) (v w : Fin 31 → ℂ) :
    headPair (M *ᵥ v) w = headPair v (Mᴴ *ᵥ w) := by
  change (∑ i, conj (∑ j, M i j*v j)*w i) =
    ∑ i, conj (v i)*(∑ j, conj (M j i)*w j)
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def headHermitianPart (M : Matrix (Fin 31) (Fin 31) ℂ) :
    Matrix (Fin 31) (Fin 31) ℂ := (1/2:ℂ) • (M+Mᴴ)

theorem head_pair_hermitian_part (M : Matrix (Fin 31) (Fin 31) ℂ) (v w : Fin 31 → ℂ) :
    headPair v (headHermitianPart M *ᵥ w) =
      (1/2:ℂ)*(headPair v (M *ᵥ w)+conj (headPair w (M *ᵥ v))) := by
  rw [← head_pair_conj_symm (M *ᵥ v) w, head_pair_mulVec_left]
  simp only [headHermitianPart, smul_mulVec, add_mulVec, headPair,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

variable (T : ℝ) [Fact (0 < T)]

noncomputable def finiteHouseholderHeadMatrix : Matrix (Fin 31) (Fin 31) ℂ :=
  headHouseholderMatrix (fun i => (finiteRotationHead i:ℂ)) (fun i => (finiteAnchorHead i:ℂ))

noncomputable def finiteBaseHeadMatrix (h h₁ h₂ : C(AddCircle T, ℂ)) (j : Fin 5) :
    Matrix (Fin 31) (Fin 31) ℂ :=
  if j = 0 then
    (finiteHouseholderHeadMatrix)ᴴ*circleHeadMatrix T (circleBlochCoefficient T h h₁ h₂ 0)*
      finiteHouseholderHeadMatrix
  else finiteTransformedHeadMatrix T (circleBlochCoefficient T h h₁ h₂ j)

noncomputable def finiteSymmetricHeadMatrix (h h₁ h₂ : C(AddCircle T, ℂ)) (j : Fin 5) :
    Matrix (Fin 31) (Fin 31) ℂ := headHermitianPart (finiteBaseHeadMatrix T h h₁ h₂ j)

theorem circle_finite_householder_head (v : Fin 31 → ℂ) :
    neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
      (circleEvenHeadH4 T v) = circleEvenHeadH4 T (finiteHouseholderHeadMatrix *ᵥ v) := by
  rw [circle_finite_rotation_phase_head, circle_anchor_head]
  exact circle_even_head_householder T _ _ v

theorem circle_finite_householder_operator_pairing
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) (v w : Fin 31 → ℂ) :
    inner ℂ
      (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
        (circleEvenHeadH4 T v) : CircleL2 T)
      (A (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
        (circleEvenHeadH4 T w))) =
      headPair v (((finiteHouseholderHeadMatrix)ᴴ*circleHeadMatrix T A*
        finiteHouseholderHeadMatrix) *ᵥ w) := by
  rw [circle_finite_householder_head, circle_finite_householder_head, circle_even_head_pairing]
  change headPair (finiteHouseholderHeadMatrix *ᵥ v)
    (circleEvenHeadCoordinates T (A (circleEvenHeadH4 T (finiteHouseholderHeadMatrix *ᵥ w)))) = _
  rw [circle_head_matrix_mulVec, head_pair_mulVec_left]
  simp only [mulVec_mulVec, mul_assoc]

theorem circle_finite_symmetric_head_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (v w : Fin 31 → ℂ) :
    circleFiniteSymmetricCoefficient T h h₁ h₂ j (circleEvenHeadH4 T v) (circleEvenHeadH4 T w) =
      headPair v (finiteSymmetricHeadMatrix T h h₁ h₂ j *ᵥ w) := by
  rw [finiteSymmetricHeadMatrix, head_pair_hermitian_part]
  by_cases hj : j = 0
  · subst j
    rw [circleFiniteSymmetricCoefficient, if_pos rfl, finiteBaseHeadMatrix, if_pos rfl]
    change (1/2:ℂ)*(inner ℂ
        (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
          (circleEvenHeadH4 T v) : CircleL2 T)
        (circleBlochCoefficient T h h₁ h₂ 0
          (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
            (circleEvenHeadH4 T w)))+
      inner ℂ (circleBlochCoefficient T h h₁ h₂ 0
          (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
            (circleEvenHeadH4 T v)))
        (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
          (circleEvenHeadH4 T w) : CircleL2 T)) = _
    rw [← inner_conj_symm
      (circleBlochCoefficient T h h₁ h₂ 0
        (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
          (circleEvenHeadH4 T v)))
      (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
        (circleEvenHeadH4 T w) : CircleL2 T)]
    rw [circle_finite_householder_operator_pairing, circle_finite_householder_operator_pairing]
  · rw [circleFiniteSymmetricCoefficient, if_neg hj, finiteBaseHeadMatrix, if_neg hj]
    rw [← inner_conj_symm
      (circleFiniteTransformedOperator T (circleBlochCoefficient T h h₁ h₂ j) (circleEvenHeadH4 T v))
      (circleEvenHeadH4 T w : CircleL2 T)]
    rw [circle_finite_transformed_head_pairing, circle_finite_transformed_head_pairing]

end Lemniscate
