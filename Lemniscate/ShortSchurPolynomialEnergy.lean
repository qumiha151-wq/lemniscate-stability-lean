import Lemniscate.ShortSchurFarRows
import Lemniscate.ShortSchurLowCertificate
import Lemniscate.ComplexRows
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The seven-dimensional certificate controls the complete quadratic form
on every finitely supported Fourier polynomial. -/
namespace Lemniscate.CoarseArithmetic
open Finset Complex Matrix
open scoped ComplexConjugate

theorem short_real_symmetric_row_form {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → ι → ℝ) (d : ι → ℝ) (v : ι → ℂ) (gap : ℝ)
    (hd : ∀ i ∈ I, 0 < d i) (hsym : ∀ i j, A i j = A j i)
    (hrow : ∀ i ∈ I, A i i + (∑ j ∈ I, if j=i then 0 else |A i j| * (d j/d i)) ≤ -gap) :
    (∑ i ∈ I, ∑ j ∈ I, conj (v i)*(A i j:ℂ)*v j).re ≤
      -gap*(∑ i ∈ I, ‖v i‖^2) := by
  let off (i j : ι) : ℂ := if j=i then 0 else (A i j:ℂ)
  have hsplit := complex_weighted_row_dissipation I (fun i => A i i) off d v gap hd
    (by
      intro i _ j _
      by_cases h : j=i
      · subst j; rfl
      · simp only [off,if_neg h,if_neg (Ne.symm h)]
        rw [hsym i j])
    (by
      intro i hi
      convert hrow i hi using 1
      congr 1
      apply sum_congr rfl
      intro j _
      by_cases h : j=i
      · simp only [off,if_pos h,norm_zero,zero_mul]
      · simp only [off,if_neg h,Complex.norm_real,Real.norm_eq_abs])
  have he (i j : ι) : conj (v i)*(A i j:ℂ)*v j =
      (if j=i then ((A i i*‖v i‖^2:ℝ):ℂ) else 0)+conj (v i)*off i j*v j := by
    by_cases h : j=i
    · subst j
      simp only [off,if_pos rfl,mul_zero,zero_mul,add_zero]
      calc
        _ = (A i i:ℂ)*(conj (v i)*v i) := by ring
        _ = _ := by rw [Complex.conj_mul']; simp only [Complex.ofReal_mul,Complex.ofReal_pow,ite_true]
    · simp only [off,if_neg h,zero_add]
  have heq : (∑ i ∈ I, ∑ j ∈ I, conj (v i)*(A i j:ℂ)*v j) =
      (∑ i ∈ I, ((A i i*‖v i‖^2:ℝ):ℂ)) +
      (∑ i ∈ I, ∑ j ∈ I, conj (v i)*off i j*v j) := by
    simp_rw [he,sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp only [sum_ite_eq',hi,ite_true]
  rw [heq]
  simpa only [Complex.add_re,← Complex.ofReal_sum,Complex.ofReal_re] using hsplit

theorem short_low_polynomial_energy (j : Fin 5) (x : Fin 7 → ℂ) :
    (∑ i : Fin 7, ∑ k : Fin 7,
      conj (x i)*(shortLowBernstein lemniscateFrequencySquared shortActualCoefficient j i k:ℂ)*x k).re ≤
      -(2/25:ℝ)*(∑ i : Fin 7, ‖x i‖^2) := by
  apply short_real_symmetric_row_form univ _ (fun i => (shortLowWeight j i:ℝ)) x (2/25)
  · intro i _
    exact_mod_cast short_low_weight_pos j i
  · intro i k
    have h : (shortLowBernstein lemniscateFrequencySquared shortActualCoefficient j)ᵀ =
        shortLowBernstein lemniscateFrequencySquared shortActualCoefficient j := by
      simp only [shortLowBernstein,transpose_mul,transpose_transpose,
        shortBernsteinHead,transpose_sum,transpose_smul,short_g_coefficient_transpose,Matrix.mul_assoc]
    exact congrFun (congrFun h k) i
  · intro i _
    exact short_low_row_bound j i

theorem short_high_polynomial_energy (j : Fin 5) (I : Finset ℤ)
    (hI : ∀ n ∈ I, 4 ≤ n.natAbs) (y : ℤ → ℂ) :
    (∑ n ∈ I, ∑ m ∈ I, conj (y n)*(shortHighEntry j n m:ℂ)*y m).re ≤
      -(5/4:ℝ)*(∑ n ∈ I, ‖y n‖^2) := by
  apply short_real_symmetric_row_form I _ (fun _ => 1) y (5/4)
  · intro _ _; norm_num
  · exact short_high_entry_symmetric j
  · intro n hn
    simpa only [div_self (by norm_num : (1:ℝ)≠0),mul_one] using
      short_all_high_row j n I (hI n hn) hI

theorem short_cross_polynomial_energy (j : Fin 5) (I : Finset ℤ)
    (hI : ∀ n ∈ I, 4 ≤ n.natAbs) (x : Fin 7 → ℂ) (y : ℤ → ℂ) :
    2*(∑ i : Fin 7, ∑ n ∈ I, conj (x i)*(shortCrossEntry j i n:ℂ)*y n).re ≤
      (7/100:ℝ)*(∑ i : Fin 7, ‖x i‖^2) + (25/28:ℝ)*(∑ n ∈ I, ‖y n‖^2) := by
  let R := ∑ i : Fin 7, ∑ n ∈ I, |shortCrossEntry j i n| * ‖x i‖*‖y n‖
  let X := ∑ i : Fin 7, ‖x i‖^2
  let Y := ∑ n ∈ I, ‖y n‖^2
  have hX : 0 ≤ X := sum_nonneg (fun _ _ => sq_nonneg _)
  have hY : 0 ≤ Y := sum_nonneg (fun _ _ => sq_nonneg _)
  have hR : 0 ≤ R := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by positivity))
  have hmajor : (∑ i : Fin 7, ∑ n ∈ I, conj (x i)*(shortCrossEntry j i n:ℂ)*y n).re ≤ R := by
    change Complex.reCLM (∑ i : Fin 7, ∑ n ∈ I,
      conj (x i)*(shortCrossEntry j i n:ℂ)*y n) ≤ R
    simp only [map_sum]
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro n _
    calc
      _ ≤ ‖conj (x i)*(shortCrossEntry j i n:ℂ)*y n‖ := Complex.re_le_norm _
      _ = _ := by simp only [norm_mul,norm_conj,Complex.norm_real,Real.norm_eq_abs]; ring
  have hc := sum_mul_sq_le_sq_mul_sq (((univ : Finset (Fin 7)) ×ˢ I))
    (fun z : Fin 7 × ℤ => |shortCrossEntry j z.1 z.2|)
    (fun z : Fin 7 × ℤ => ‖x z.1‖*‖y z.2‖)
  have hleft : (∑ z ∈ ((univ : Finset (Fin 7)) ×ˢ I), |shortCrossEntry j z.1 z.2| * (‖x z.1‖*‖y z.2‖)) = R := by
    have hp := Finset.sum_product (univ:Finset (Fin 7)) I
      (fun z : Fin 7 × ℤ => |shortCrossEntry j z.1 z.2| * (‖x z.1‖*‖y z.2‖))
    simpa only [R,mul_assoc] using hp
  have hright : (∑ z ∈ ((univ : Finset (Fin 7)) ×ˢ I), (‖x z.1‖*‖y z.2‖)^2) = X*Y := by
    have hp := Finset.sum_product (univ:Finset (Fin 7)) I
      (fun z : Fin 7 × ℤ => (‖x z.1‖*‖y z.2‖)^2)
    exact hp.trans (by simp only [mul_pow,← mul_sum,← sum_mul,X,Y])
  rw [hleft,hright] at hc
  have hhs := short_all_cross_square j I hI
  have hsum : (∑ z ∈ ((univ : Finset (Fin 7)) ×ˢ I), |shortCrossEntry j z.1 z.2|^2) ≤ (1/16:ℝ) := by
    rw [Finset.sum_product (univ:Finset (Fin 7)) I
      (fun z : Fin 7 × ℤ => |shortCrossEntry j z.1 z.2|^2)]
    exact hhs
  have hr2 : R^2 ≤ (1/16:ℝ)*X*Y :=
    hc.trans (by have ht := mul_le_mul_of_nonneg_right hsum (mul_nonneg hX hY); nlinarith only [ht])
  have hbound : 2*R ≤ (7/100:ℝ)*X+(25/28:ℝ)*Y := by
    nlinarith [sq_nonneg ((7/100:ℝ)*X-(25/28:ℝ)*Y)]
  exact (mul_le_mul_of_nonneg_left hmajor (by norm_num)).trans hbound

theorem short_schur_polynomial_energy (j : Fin 5) (I : Finset ℤ)
    (hI : ∀ n ∈ I, 4 ≤ n.natAbs) (x : Fin 7 → ℂ) (y : ℤ → ℂ) :
    (∑ i : Fin 7, ∑ k : Fin 7,
      conj (x i)*(shortLowBernstein lemniscateFrequencySquared shortActualCoefficient j i k:ℂ)*x k).re +
    2*(∑ i : Fin 7, ∑ n ∈ I, conj (x i)*(shortCrossEntry j i n:ℂ)*y n).re +
    (∑ n ∈ I, ∑ m ∈ I, conj (y n)*(shortHighEntry j n m:ℂ)*y m).re ≤
      -(1/100:ℝ)*((∑ i : Fin 7, ‖x i‖^2)+(∑ n ∈ I, ‖y n‖^2)) := by
  have hl := short_low_polynomial_energy j x
  have hh := short_high_polynomial_energy j I hI y
  have hc := short_cross_polynomial_energy j I hI x y
  have hY : (0:ℝ) ≤ ∑ n ∈ I, ‖y n‖^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

end Lemniscate.CoarseArithmetic
