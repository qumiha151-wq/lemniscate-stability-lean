import Lemniscate.PeriodicHeadCompression
import Lemniscate.PeriodicBlochCoefficientFourier

/-! Identify the actual finite neutral conjugation and the Fourier coefficient
matrices. Development source for the shorter even Bloch proof. -/
namespace Lemniscate
open Complex MeasureTheory Matrix CoarseArithmetic
open scoped ComplexConjugate

noncomputable def finiteRotationHead (i : Fin 31) : ℝ :=
  finiteSineCoordinate rotationFiniteCoefficient i

noncomputable def finiteAdjointHead (i : Fin 31) : ℝ :=
  finiteSineCoordinate adjointFiniteCoefficient i

noncomputable def finiteAnchorHead (i : Fin 31) : ℝ :=
  (1/Real.sqrt 2)*((if evenHeadFrequency i = 2 then 1 else 0)-
    (if evenHeadFrequency i = -2 then 1 else 0))

variable (T : ℝ) [Fact (0 < T)]

theorem circle_anchor_head : circleHouseholderAnchorH4 T =
    circleEvenHeadH4 T (fun i => (finiteAnchorHead i:ℂ)) := by
  have hs (n : ℤ) (hn : ¬(Even n ∧ |(n:ℝ)| < 32)) :
      fourierCoeff (circleHouseholderAnchorH4 T : CircleL2 T) n = 0 := by
    have hp : n ≠ 2 := by
      rintro rfl
      exact hn ((even_head_frequency_range 2).mp ⟨(16:Fin 31), by norm_num [evenHeadFrequency]⟩)
    have hm : n ≠ -2 := by
      rintro rfl
      exact hn ((even_head_frequency_range (-2)).mp ⟨(14:Fin 31), by norm_num [evenHeadFrequency]⟩)
    rw [circle_householder_anchor_h4_coe, circle_householder_anchor_fourier,
      if_neg hp, if_neg hm]
    ring
  have hp := circle_even_head_projection_of_support T (circleHouseholderAnchorH4 T) hs
  calc
    circleHouseholderAnchorH4 T = circleEvenHeadProjection T (circleHouseholderAnchorH4 T) := hp.symm
    _ = _ := by
      unfold circleEvenHeadProjection
      congr 1
      funext i
      rw [circle_householder_anchor_h4_coe, circle_householder_anchor_fourier]
      unfold finiteAnchorHead evenCosineFactor
      split_ifs <;> push_cast <;> ring

noncomputable def finiteTransformedHeadMatrix
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) : Matrix (Fin 31) (Fin 31) ℂ :=
  let e := fun i => (finiteRotationHead i:ℂ)
  let p := fun i => (finiteAdjointHead i:ℂ)
  let a := fun i => (finiteAnchorHead i:ℂ)
  headHouseholderMatrix e a*headNeutralMatrix e p*circleHeadMatrix T A*
    headNeutralInvMatrix e p*headHouseholderMatrix e a

theorem circle_finite_transformed_head_pairing
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) (v w : Fin 31 → ℂ) :
    inner ℂ (circleEvenHeadH4 T v : CircleL2 T)
      (circleFiniteTransformedOperator T A (circleEvenHeadH4 T w)) =
      headPair v (finiteTransformedHeadMatrix T A *ᵥ w) := by
  change inner ℂ (circleEvenHeadH4 T v : CircleL2 T)
    (neutralHouseholder (circleFiniteRotationPhase T : CircleL2 T) (circleHouseholderAnchor T)
      (neutralTransform (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
        (A (neutralTransformInvDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
          (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
            (circleEvenHeadH4 T w)))))) = _
  rw [← circle_householder_anchor_h4_coe T]
  rw [circle_finite_rotation_phase_head, circle_finite_adjoint_phase_head, circle_anchor_head]
  exact circle_head_transformed_pairing T _ _ _ v w A

noncomputable def evenBlochCoefficientMatrix (r q : ℝ) (j : Fin 5) :
    Matrix (Fin 31) (Fin 31) ℝ := fun i k =>
  let n := (evenHeadFrequency i:ℝ)
  let m := (evenHeadFrequency k:ℝ)
  let c := fourierCoefficient r q ((evenHeadFrequency i-evenHeadFrequency k).natAbs/2)
  let d : ℝ := if i = k then 1 else 0
  ![(-4*r^2*m^4-42)*d+(15/2:ℝ)*r*n*(7*m-n)*c,
    (-16*r^2*m^3)*d+r*((75/2:ℝ)*n+(105/2:ℝ)*m)*c,
    (-24*r^2*m^2)*d+45*r*c,
    (-16*r^2*m)*d, (-4*r^2)*d] j

theorem circle_head_bloch_coefficient_matrix (h h₁ h₂ : C(AddCircle T, ℂ)) (r q : ℝ)
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient r q j:ℂ))
    (hr : (2*Real.pi/T)^2 = r) (j : Fin 5) :
    circleHeadMatrix T (circleBlochCoefficient T h h₁ h₂ j) =
      fun i k => (evenBlochCoefficientMatrix r q j i k:ℂ) := by
  funext i k
  rw [circleHeadMatrix, circle_bloch_coefficient_basis_pairing T h h₁ h₂ hh hh₁]
  have hdiff : evenHeadFrequency i-evenHeadFrequency k = 2*((i.val:ℤ)-(k.val:ℤ)) := by
    dsimp only [evenHeadFrequency]
    omega
  have hd : fourierCoeff h (evenHeadFrequency i-evenHeadFrequency k) =
      (fourierCoefficient r q ((evenHeadFrequency i-evenHeadFrequency k).natAbs/2):ℂ) := by
    rw [hdiff, circle_even_integer_coefficient T h r q hs hc]
    simp [Int.natAbs_mul]
  fin_cases j <;>
    simp only [circleBlochCoefficientEntry, evenBlochCoefficientMatrix, hr, hd,
      even_head_frequency_injective.eq_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;>
    split_ifs <;> push_cast <;> ring

end Lemniscate
