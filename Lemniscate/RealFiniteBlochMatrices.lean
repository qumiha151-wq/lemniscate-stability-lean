import Lemniscate.RealHeadMatrices

/-! Pure real versions of the actual finite Bernstein matrices. These are
the real-number expressions enclosed by the rational interval calculation. -/
namespace Lemniscate
open Complex Matrix MeasureTheory

noncomputable def realFiniteBaseHead (r q : ℝ) (j : Fin 5) : Matrix (Fin 31) (Fin 31) ℝ :=
  if j = 0 then realFiniteHouseholderᵀ*evenBlochCoefficientMatrix r q 0*realFiniteHouseholder
  else realFiniteHouseholder*realFiniteNeutral*evenBlochCoefficientMatrix r q j*
    realFiniteNeutralInv*realFiniteHouseholder

noncomputable def realFiniteSymmetricHead (r q : ℝ) (j : Fin 5) : Matrix (Fin 31) (Fin 31) ℝ :=
  realHeadHermitianPart (realFiniteBaseHead r q j)

noncomputable def realFiniteBlochCoefficient (r q : ℝ) (j : Fin 5) :
    Matrix (Fin 31) (Fin 31) ℝ :=
  let H := realFiniteSymmetricHead r q
  let P₀ := realFiniteAnchorProjection
  let P := realFiniteStableProjection
  let c : ℝ := -4*r^2
  ![P₀ᵀ*H 2*P₀+(P₀ᵀ*H 1*P+Pᵀ*H 1*P₀)+Pᵀ*H 0*P,
    (P₀ᵀ*H 2*P+Pᵀ*H 2*P₀)+Pᵀ*H 1*P,
    c • (P₀ᵀ*P₀)+(P₀ᵀ*H 3*P+Pᵀ*H 3*P₀)+Pᵀ*H 2*P,
    Pᵀ*H 3*P, c • (Pᵀ*P)] j

noncomputable def realFiniteBlochBernstein (r q : ℝ) (k : Fin 5) :
    Matrix (Fin 31) (Fin 31) ℝ :=
  realQuarticMatrixBernstein (realFiniteBlochCoefficient r q) k

variable (T : ℝ) [Fact (0 < T)]
variable (h h₁ h₂ : C(AddCircle T, ℂ)) (r q : ℝ)
variable (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
variable (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
variable (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (CoarseArithmetic.fourierCoefficient r q j:ℂ))
variable (hr : (2*Real.pi/T)^2 = r)
include hh hh₁ hs hc hr

theorem real_finite_base_head_cast (j : Fin 5) :
    realHeadMatrixCast (realFiniteBaseHead r q j) = finiteBaseHeadMatrix T h h₁ h₂ j := by
  have hA (l : Fin 5) : circleHeadMatrix T (circleBlochCoefficient T h h₁ h₂ l) =
      realHeadMatrixCast (evenBlochCoefficientMatrix r q l) :=
    circle_head_bloch_coefficient_matrix T h h₁ h₂ r q hh hh₁ hs hc hr l
  unfold realFiniteBaseHead finiteBaseHeadMatrix
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos hj]
    simp only [map_mul, real_head_matrix_cast_transpose, real_finite_householder_cast, hA]
  · rw [if_neg hj, if_neg hj]
    simp only [finiteTransformedHeadMatrix, map_mul, realFiniteNeutral,
      realFiniteNeutralInv, real_head_neutral_cast, real_head_neutral_inv_cast,
      real_finite_householder_cast, finiteHouseholderHeadMatrix, hA]

theorem real_finite_symmetric_head_cast (j : Fin 5) :
    realHeadMatrixCast (realFiniteSymmetricHead r q j) =
      finiteSymmetricHeadMatrix T h h₁ h₂ j := by
  rw [realFiniteSymmetricHead, real_head_hermitian_part_cast,
    real_finite_base_head_cast T h h₁ h₂ r q hh hh₁ hs hc hr]
  rfl

theorem real_finite_bloch_coefficient_cast (j : Fin 5) :
    realHeadMatrixCast (realFiniteBlochCoefficient r q j) =
      finiteBlochHeadCoefficient T h h₁ h₂ j := by
  have hr₄ : (2*Real.pi/T)^4 = r^2 := by
    calc
      _ = ((2*Real.pi/T)^2)^2 := by ring
      _ = _ := by rw [hr]
  have hH := real_finite_symmetric_head_cast T h h₁ h₂ r q hh hh₁ hs hc hr
  fin_cases j <;>
    norm_num [realFiniteBlochCoefficient, finiteBlochHeadCoefficient,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons, map_add, map_mul,
      real_head_matrix_cast_smul, real_head_matrix_cast_transpose,
      real_finite_anchor_projection_cast, real_finite_stable_projection_cast, hH, hr₄]

theorem real_finite_bloch_bernstein_cast (k : Fin 5) :
    realHeadMatrixCast (realFiniteBlochBernstein r q k) =
      finiteBlochHeadBernstein T h h₁ h₂ k := by
  rw [realFiniteBlochBernstein, real_quartic_matrix_bernstein_cast]
  exact congrArg (fun C => quarticMatrixBernstein C k)
    (funext (fun j => real_finite_bloch_coefficient_cast T h h₁ h₂ r q hh hh₁ hs hc hr j))

end Lemniscate
