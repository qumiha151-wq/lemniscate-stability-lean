import Lemniscate.ShortHeadCompression
import Lemniscate.ShortSchurSymmetry

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

noncomputable def shortComplexMatrix {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℂ := fun i j => (M i j:ℂ)

theorem short_complex_matrix_mul {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    shortComplexMatrix (A*B)=shortComplexMatrix A*shortComplexMatrix B := by
  ext i j
  simp [shortComplexMatrix,Matrix.mul_apply]

theorem short_householder_matrix_real (h : ℕ → ℝ) :
    shortHeadHouseholderMatrix (fun i => (shortRotationHead h i:ℂ))
      (fun i => (shortAnchorHead i:ℂ)) = shortComplexMatrix (shortHouseholder h) := by
  ext i j
  simp [shortHeadHouseholderMatrix,shortHeadPair,shortComplexMatrix,
    shortHouseholder,shortOuter,Matrix.one_apply,Pi.add_apply]
  push_cast
  split_ifs <;> norm_num <;> ring

theorem short_neutral_matrix_real (h : ℕ → ℝ) :
    shortHeadNeutralMatrix (fun i => (shortRotationHead h i:ℂ))
      (fun i => (shortAdjointHead h i:ℂ)) = shortComplexMatrix (shortNeutral h) := by
  ext i j
  simp [shortHeadNeutralMatrix,shortComplexMatrix,shortNeutral,shortOuter,Matrix.one_apply]
  split_ifs <;> push_cast <;> ring

theorem short_neutral_inv_matrix_real (h : ℕ → ℝ) :
    shortHeadNeutralInvMatrix (fun i => (shortRotationHead h i:ℂ))
      (fun i => (shortAdjointHead h i:ℂ)) = shortComplexMatrix (shortNeutralInv h) := by
  ext i j
  simp [shortHeadNeutralInvMatrix,shortComplexMatrix,shortNeutralInv,shortOuter,Matrix.one_apply]
  split_ifs <;> push_cast <;> ring

variable (T : ℝ) [Fact (0<T)]

theorem circle_short_bloch_head_matrix (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (d : ℕ → ℝ) (r : ℝ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ))=(d j:ℂ))
    (hr : (2*Real.pi/T)^2=r) (j : Fin 5) :
    circleShortHeadMatrix T (circleBlochCoefficient T h h₁ h₂ j) =
      shortComplexMatrix (shortBlochHead r d j) := by
  ext i k
  have hf (a : Fin 15) : shortHeadFrequency a=2*((a.val:ℤ)-7) := by
    dsimp only [shortHeadFrequency]
    ring
  change inner ℂ (fourierBasis (T:=T) (shortHeadFrequency i))
    (circleBlochCoefficient T h h₁ h₂ j (circleFourierH4 T (shortHeadFrequency k))) =
      (shortBlochEntry r d j (shortHeadFrequency i) (shortHeadFrequency k):ℂ)
  simp only [hf]
  exact short_circle_bloch_basis_pairing T h h₁ h₂ hh hh₁ d r hs hc hr j _ _

theorem circle_short_transformed_head_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ))=(shortActualCoefficient j:ℂ))
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)
    (j : Fin 5) (v w : Fin 15 → ℂ) :
    inner ℂ (circleShortHead T v:CircleL2 T)
      (circleShortTransformedCoefficient T h h₁ h₂ j (circleShortHead T w)) =
      shortHeadPair v (shortComplexMatrix
        (shortHouseholder shortActualCoefficient * shortNeutral shortActualCoefficient *
          shortBlochHead lemniscateFrequencySquared shortActualCoefficient j *
          shortNeutralInv shortActualCoefficient * shortHouseholder shortActualCoefficient) *ᵥ w) := by
  unfold circleShortTransformedCoefficient circleShortHouseholder circleShortHouseholderH4
  rw [← circle_householder_anchor_h4_coe T, circle_short_rotation_head,
    circle_short_adjoint_head, circle_short_anchor_head]
  rw [circle_short_head_transformed_pairing,short_householder_matrix_real,
    short_neutral_matrix_real,short_neutral_inv_matrix_real,
    circle_short_bloch_head_matrix T h h₁ h₂ hh hh₁ _ _ hs hc hr]
  simp only [short_complex_matrix_mul]

end Lemniscate
