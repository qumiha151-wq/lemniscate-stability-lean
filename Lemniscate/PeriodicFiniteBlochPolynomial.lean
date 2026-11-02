import Lemniscate.PeriodicFiniteBlochMatrix
import Lemniscate.Bernstein

/-! Quartic coefficients of the actual finite reduced form. The five
Bernstein matrices use the same direct products as the interval certificate. -/
namespace Lemniscate
open Complex Matrix

variable (T : ℝ) [Fact (0 < T)]

noncomputable def finiteBlochHeadCoefficient (h h₁ h₂ : C(AddCircle T, ℂ)) (j : Fin 5) :
    Matrix (Fin 31) (Fin 31) ℂ :=
  let H := finiteSymmetricHeadMatrix T h h₁ h₂
  let P₀ := finiteAnchorProjection
  let P := finiteStableProjection
  let c : ℂ := ((-4*(2*Real.pi/T)^4:ℝ):ℂ)
  ![P₀ᴴ*H 2*P₀+(P₀ᴴ*H 1*P+Pᴴ*H 1*P₀)+Pᴴ*H 0*P,
    (P₀ᴴ*H 2*P+Pᴴ*H 2*P₀)+Pᴴ*H 1*P,
    c • (P₀ᴴ*P₀)+(P₀ᴴ*H 3*P+Pᴴ*H 3*P₀)+Pᴴ*H 2*P,
    Pᴴ*H 3*P, c • (Pᴴ*P)] j

theorem finite_bloch_head_polynomial (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) :
    finiteBlochHeadMatrix T h h₁ h₂ α =
      finiteBlochHeadCoefficient T h h₁ h₂ 0+
      (α:ℂ) • finiteBlochHeadCoefficient T h h₁ h₂ 1+
      (α:ℂ)^2 • finiteBlochHeadCoefficient T h h₁ h₂ 2+
      (α:ℂ)^3 • finiteBlochHeadCoefficient T h h₁ h₂ 3+
      (α:ℂ)^4 • finiteBlochHeadCoefficient T h h₁ h₂ 4 := by
  simp only [finiteBlochHeadMatrix, finiteBlochHeadCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons]
  module

noncomputable def quarticMatrixBernstein (C : Fin 5 → Matrix (Fin 31) (Fin 31) ℂ) (k : Fin 5) :
    Matrix (Fin 31) (Fin 31) ℂ :=
  ![C 0,
    C 0+(1/8:ℂ) • C 1,
    C 0+(1/4:ℂ) • C 1+(1/24:ℂ) • C 2,
    C 0+(3/8:ℂ) • C 1+(1/8:ℂ) • C 2+(1/32:ℂ) • C 3,
    C 0+(1/2:ℂ) • C 1+(1/4:ℂ) • C 2+(1/8:ℂ) • C 3+(1/16:ℂ) • C 4] k

set_option maxHeartbeats 2000000 in
theorem quartic_matrix_bernstein (C : Fin 5 → Matrix (Fin 31) (Fin 31) ℂ) (α : ℝ) :
    C 0+(α:ℂ) • C 1+(α:ℂ)^2 • C 2+(α:ℂ)^3 • C 3+(α:ℂ)^4 • C 4 =
      ∑ k : Fin 5, (bernsteinBasis 4 k.val α:ℂ) • quarticMatrixBernstein C k := by
  norm_num [quarticMatrixBernstein, bernsteinBasis, bernsteinPolynomial,
    Fin.sum_univ_succ, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_natCast, Nat.choose]
  push_cast
  module

noncomputable def finiteBlochHeadBernstein (h h₁ h₂ : C(AddCircle T, ℂ)) (k : Fin 5) :
    Matrix (Fin 31) (Fin 31) ℂ :=
  quarticMatrixBernstein (finiteBlochHeadCoefficient T h h₁ h₂) k

theorem finite_bloch_head_bernstein (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) :
    finiteBlochHeadMatrix T h h₁ h₂ α =
      ∑ k : Fin 5, (bernsteinBasis 4 k.val α:ℂ) • finiteBlochHeadBernstein T h h₁ h₂ k := by
  rw [finite_bloch_head_polynomial]
  exact quartic_matrix_bernstein _ α

end Lemniscate
