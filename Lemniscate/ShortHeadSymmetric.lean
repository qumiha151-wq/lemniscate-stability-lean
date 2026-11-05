import Lemniscate.ShortHeadMatrices
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

theorem short_head_pair_conj_symm {N : ℕ} (v w : Fin N → ℂ) :
    shortHeadPair v w=conj (shortHeadPair w v) := by
  simp only [shortHeadPair,map_sum,map_mul,conj_conj]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem short_head_pair_mulVec_left {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (v w : Fin N → ℂ) : shortHeadPair (M*ᵥv) w=shortHeadPair v (Mᴴ*ᵥw) := by
  change (∑ i, conj (∑ j, M i j*v j)*w i)=
    ∑ i, conj (v i)*(∑ j,conj (M j i)*w j)
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem short_complex_matrix_conjTranspose {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    (shortComplexMatrix M)ᴴ=shortComplexMatrix Mᵀ := by
  ext i j
  simp [shortComplexMatrix,Matrix.conjTranspose_apply]

theorem short_head_pair_symmetric (M : Matrix (Fin 15) (Fin 15) ℝ)
    (v w : Fin 15 → ℂ) :
    shortHeadPair v (shortComplexMatrix (shortSymmetric M)*ᵥw)=
      (1/2:ℂ)*(shortHeadPair v (shortComplexMatrix M*ᵥw)+
        conj (shortHeadPair w (shortComplexMatrix M*ᵥv))) := by
  rw [← short_head_pair_conj_symm (shortComplexMatrix M*ᵥv) w,
    short_head_pair_mulVec_left,short_complex_matrix_conjTranspose]
  simp only [shortHeadPair,shortComplexMatrix,shortSymmetric,Matrix.mulVec,
    dotProduct,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul]
  push_cast
  simp only [mul_add,add_mul,Finset.mul_sum,Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem short_symmetric_householder_product (h : ℕ → ℝ)
    (A : Matrix (Fin 15) (Fin 15) ℝ) :
    shortSymmetric (shortHouseholder h*A*shortHouseholder h)=
      shortHouseholder h*shortSymmetric A*shortHouseholder h := by
  simp only [shortSymmetric,Matrix.transpose_mul,short_householder_transpose,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_add,Matrix.add_mul,mul_assoc]

variable (T : ℝ) [Fact (0<T)]

theorem circle_short_head_operator_pairing (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (v w : Fin 15 → ℂ) :
    inner ℂ (circleShortHead T v:CircleL2 T) (A (circleShortHead T w))=
      shortHeadPair v (circleShortHeadMatrix T A*ᵥw) := by
  rw [circle_short_head_pairing]
  change shortHeadPair v (circleShortHeadCoordinates T (A (circleShortHead T w)))=_
  rw [circle_short_head_matrix_mulVec]

theorem circle_short_householder_head (v : Fin 15 → ℂ) :
    circleShortHouseholderH4 T (circleShortHead T v)=
      circleShortHead T (shortComplexMatrix (shortHouseholder shortActualCoefficient)*ᵥv) := by
  unfold circleShortHouseholderH4
  rw [circle_short_rotation_head,circle_short_anchor_head,circle_short_head_householder,
    short_householder_matrix_real]

theorem circle_short_zero_symmetric (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x,conj (h x)=h x) (h₁real : ∀ x,conj (h₁ x)=h₁ x)
    (h₂real : ∀ x,conj (h₂ x)=h₂ x) (f g : circleH4Domain T) :
    circleShortSymmetricCoefficient T h h₁ h₂ 0 f g =
      (1/2:ℂ)*(inner ℂ (circleShortHouseholderH4 T f:CircleL2 T)
        (circleBlochCoefficient T h h₁ h₂ 0 (circleShortHouseholderH4 T g))+
        inner ℂ (circleBlochCoefficient T h h₁ h₂ 0 (circleShortHouseholderH4 T f))
          (circleShortHouseholderH4 T g:CircleL2 T)) := by
  let Uf := circleShortHouseholderH4 T f
  let Ug := circleShortHouseholderH4 T g
  change inner ℂ (Uf:CircleL2 T) (circleH4SymmetricOperator T h h₁ h₂ Ug)=
    (1/2:ℂ)*(inner ℂ (Uf:CircleL2 T) (circleH4Operator T h h₁ h₂ Ug)+
      inner ℂ (circleH4Operator T h h₁ h₂ Uf) (Ug:CircleL2 T))
  rw [circle_h4_formal_adjoint_green T h h₁ h₂ hh hh₁ hreal h₁real h₂real Uf Ug,
    circle_h4_formal_adjoint_split T h h₁ h₂ Ug,circle_h4_operator_apply]
  unfold circleLinearL2Expression
  rw [← circle_h4_symmetric_operator_apply T h h₁ h₂ Ug]
  simp only [inner_add_right,inner_sub_right]
  ring

end Lemniscate
