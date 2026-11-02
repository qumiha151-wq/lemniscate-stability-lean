import Lemniscate.PeriodicBlochCoefficientFourier
import Lemniscate.PeriodicBlochGreen

/-! Off-diagonal bounds for the actual Bloch coefficients and their formal
adjoints. Low input modes have absolute value at most 20; high output modes
have absolute value at least 32. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

private theorem low_high_scalar_bounds (r x y : ℝ) (hr : 0 ≤ r) (hru : r ≤ 18/25)
    (hx : |x| ≤ 20) (hy : 32 ≤ |y|) :
    |(15/2)*r*y*(7*x-y)| ≤ 30*y^2 ∧
    |(15/2)*r*x*(7*y-x)| ≤ 30*y^2 ∧
    |r*((75/2)*y+(105/2)*x)| ≤ 30*y^2 ∧
    |r*((75/2)*x+(105/2)*y)| ≤ 30*y^2 ∧
    |45*r| ≤ 30*y^2 := by
  have hxy : |x| ≤ (5/8)*|y| := by linarith only [hx,hy]
  have hy0 := abs_nonneg y
  have hysq := sq_abs y
  have hquad := mul_nonneg hy0 (sub_nonneg.mpr hy)
  have hs (a b : ℝ) : |7*a-b| ≤ 7*|a|+|b| := by
    simpa only [abs_mul,show |(7:ℝ)| = 7 by norm_num] using abs_sub (7*a) b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ = (15/2)*r*|y| * |7*x-y| := by
        simp only [abs_mul,abs_of_nonneg hr]; norm_num
      _ ≤ (15/2)*r*|y| * (7*|x|+|y|) := by gcongr; exact hs x y
      _ ≤ (15/2)*(18/25)*|y| * (7*((5/8)*|y|)+|y|) := by gcongr
      _ ≤ _ := by nlinarith only [hysq,sq_nonneg y]
  · calc
      _ = (15/2)*r*|x| * |7*y-x| := by
        simp only [abs_mul,abs_of_nonneg hr]; norm_num
      _ ≤ (15/2)*r*|x| * (7*|y|+|x|) := by gcongr; exact hs y x
      _ ≤ (15/2)*(18/25)*((5/8)*|y|)*(7*|y|+(5/8)*|y|) := by gcongr
      _ ≤ _ := by nlinarith only [hysq,sq_nonneg y]
  · calc
      _ = r*|(75/2)*y+(105/2)*x| := by rw [abs_mul,abs_of_nonneg hr]
      _ ≤ r*((75/2)*|y|+(105/2)*|x|) := by
        gcongr
        convert abs_add_le ((75/2:ℝ)*y) ((105/2:ℝ)*x) using 1 <;> norm_num [abs_mul]
      _ ≤ (18/25)*((75/2)*|y|+(105/2)*((5/8)*|y|)) := by gcongr
      _ ≤ _ := by nlinarith only [hysq,hquad,hy0]
  · calc
      _ = r*|(75/2)*x+(105/2)*y| := by rw [abs_mul,abs_of_nonneg hr]
      _ ≤ r*((75/2)*|x|+(105/2)*|y|) := by
        gcongr
        convert abs_add_le ((75/2:ℝ)*x) ((105/2:ℝ)*y) using 1 <;> norm_num [abs_mul]
      _ ≤ (18/25)*((75/2)*((5/8)*|y|)+(105/2)*|y|) := by gcongr
      _ ≤ _ := by nlinarith only [hysq,hquad,hy0]
  · rw [abs_mul,abs_of_nonneg hr]
    norm_num
    nlinarith only [hru,hysq,hquad,hy]

variable (T : ℝ) [Fact (0 < T)]

theorem circle_bloch_low_high_entry_bound (h : C(AddCircle T, ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25) (j : Fin 5) (n m : ℤ)
    (hn : 32 ≤ |(n:ℝ)|) (hm : |(m:ℝ)| ≤ 20) :
    ‖circleBlochCoefficientEntry T h j n m‖ ≤
      30*(n:ℝ)^2*‖fourierCoeff h (n-m)‖ ∧
    ‖circleBlochCoefficientEntry T h j m n‖ ≤
      30*(n:ℝ)^2*‖fourierCoeff h (m-n)‖ := by
  have hnm : n ≠ m := by intro heq; subst n; linarith only [hn,hm]
  have hmn : m ≠ n := Ne.symm hnm
  have hb := low_high_scalar_bounds ((2*Real.pi/T)^2) (m:ℝ) (n:ℝ)
    (sq_nonneg _) hr hm hn
  fin_cases j <;> norm_num only [circleBlochCoefficientEntry,
    if_neg hnm,if_neg hmn,mul_zero,zero_add,
    Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_one,Matrix.cons_val,
    Matrix.head_cons,Matrix.tail_cons]
  · constructor
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hb.1 (norm_nonneg _)
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hb.2.1 (norm_nonneg _)
  · constructor
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hb.2.2.1 (norm_nonneg _)
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hb.2.2.2.1 (norm_nonneg _)
  · constructor <;> rw [norm_mul,Complex.norm_real,Real.norm_eq_abs] <;>
      exact mul_le_mul_of_nonneg_right hb.2.2.2.2 (norm_nonneg _)
  · constructor <;> simp only [norm_zero] <;> positivity
  · constructor <;> simp only [norm_zero] <;> positivity

theorem circle_bloch_adjoint_basis_fourier (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (j : Fin 5) (n m : ℤ) :
    fourierCoeff (circleBlochAdjointCoefficient T h h₁ h₂ j (circleFourierH4 T m)) n =
      conj (circleBlochCoefficientEntry T h j m n) := by
  have hg := circle_bloch_coefficient_green T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    j (circleFourierH4 T n) (circleFourierH4 T m)
  change inner ℂ (circleBlochCoefficient T h h₁ h₂ j (circleFourierH4 T n))
      (fourierBasis (T := T) m) =
    inner ℂ (fourierBasis (T := T) n)
      (circleBlochAdjointCoefficient T h h₁ h₂ j (circleFourierH4 T m)) at hg
  rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr] at hg
  rw [← hg,← inner_conj_symm _ (fourierBasis (T := T) m),
    circle_bloch_coefficient_basis_pairing T h h₁ h₂ hh hh₁]

end Lemniscate
