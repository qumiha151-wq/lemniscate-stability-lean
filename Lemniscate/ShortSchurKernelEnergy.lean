import Lemniscate.ShortSchurCoordinateNorms

namespace Lemniscate.CoarseArithmetic
open Matrix Finset Complex
open scoped ComplexConjugate

noncomputable def shortLowFourierCoordinates (x : Fin 7 → ℂ) (a : Fin 15) : ℂ :=
  ∑ k : Fin 7, (shortLowEmbedding a k:ℂ)*x k

private theorem real_matrix_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Matrix ι κ ℝ) (B : Matrix ι ι ℝ) (x : κ → ℂ) :
    (∑ a : ι, ∑ b : ι,
      conj (∑ k : κ, (F a k:ℂ)*x k)*(B a b:ℂ)*(∑ k : κ, (F b k:ℂ)*x k)) =
      ∑ i : κ, ∑ k : κ, conj (x i)*((Fᵀ*B*F) i k:ℂ)*x k := by
  let A := F.map Complex.ofRealHom
  let C := B.map Complex.ofRealHom
  have hc : (fun a => conj ((A *ᵥ x) a)) = A *ᵥ (fun k => conj (x k)) := by
    funext a
    simp only [Matrix.mulVec,dotProduct,A,Matrix.map_apply,map_sum,map_mul,
      Complex.ofRealHom_eq_coe,Complex.conj_ofReal]
  have hG : Aᵀ*(C*A) = (Fᵀ*B*F).map Complex.ofRealHom := by
    rw [Matrix.map_mul,Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rfl
  have hh : (fun a => conj ((A *ᵥ x) a)) ⬝ᵥ (C *ᵥ (A *ᵥ x)) =
      (fun k => conj (x k)) ⬝ᵥ ((Fᵀ*B*F).map Complex.ofRealHom *ᵥ x) := by
    rw [hc,Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_mulVec,
      ← Matrix.dotProduct_mulVec,hG]
  simpa only [Matrix.mulVec,dotProduct,A,C,Matrix.map_apply,Complex.ofRealHom_eq_coe,
    mul_sum,mul_assoc] using hh

theorem short_embedded_low_kernel (j : Fin 5) (x : Fin 7 → ℂ) :
    (∑ a : Fin 15, ∑ b : Fin 15,
      conj (shortLowFourierCoordinates x a)*
        (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j
          ((a.val:ℤ)-7) ((b.val:ℤ)-7):ℂ)*shortLowFourierCoordinates x b) =
      ∑ i : Fin 7, ∑ k : Fin 7,
        conj (x i)*(shortLowBernstein lemniscateFrequencySquared shortActualCoefficient j i k:ℂ)*x k := by
  simp only [shortBernsteinKernel,short_head_index_half,shortLowFourierCoordinates]
  exact real_matrix_congruence shortLowEmbedding
    (shortBernsteinHead lemniscateFrequencySquared shortActualCoefficient j) x

theorem short_embedded_cross_kernel (j : Fin 5) (I : Finset ℤ)
    (x : Fin 7 → ℂ) (y : ℤ → ℂ) :
    (∑ a : Fin 15, ∑ n ∈ I, conj (shortLowFourierCoordinates x a)*
      (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j ((a.val:ℤ)-7) n:ℂ)*
        (y n/(((2*(n:ℝ))^2:ℝ):ℂ))) =
      ∑ i : Fin 7, ∑ n ∈ I, conj (x i)*(shortCrossEntry j i n:ℂ)*y n := by
  have heq (n : ℤ) : (∑ a : Fin 15, conj (shortLowFourierCoordinates x a)*
      (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j ((a.val:ℤ)-7) n:ℂ)*
        (y n/(((2*(n:ℝ))^2:ℝ):ℂ))) =
      ∑ i : Fin 7, conj (x i)*(shortCrossEntry j i n:ℂ)*y n := by
    simp only [shortLowFourierCoordinates,shortCrossEntry,map_sum,map_mul,Complex.conj_ofReal,
      Complex.ofReal_sum,Complex.ofReal_mul,div_eq_mul_inv,sum_mul,mul_sum]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro a _
    push_cast
    ring
  rw [Finset.sum_comm]
  simp only [heq]
  rw [Finset.sum_comm]

theorem short_embedded_high_kernel (j : Fin 5) (I : Finset ℤ) (y : ℤ → ℂ) :
    (∑ n ∈ I, ∑ m ∈ I, conj (y n/(((2*(n:ℝ))^2:ℝ):ℂ))*
      (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j n m:ℂ)*
        (y m/(((2*(m:ℝ))^2:ℝ):ℂ))) =
      ∑ n ∈ I, ∑ m ∈ I, conj (y n)*(shortHighEntry j n m:ℂ)*y m := by
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro m _
  simp only [shortHighEntry,Complex.ofReal_mul,
    div_eq_mul_inv,_root_.mul_inv_rev]
  push_cast
  simp only [map_mul,map_inv₀,map_pow,map_intCast,map_ofNat]
  ring

theorem short_max_fourth_eq_square (t : ℝ) :
    max 1 (t^4) = (max 1 (t^2))^2 := by
  by_cases h : 1 ≤ t^2
  · rw [max_eq_right h,max_eq_right (by nlinarith : (1:ℝ)≤t^4)]
    ring
  · rw [max_eq_left (not_le.mp h).le,max_eq_left (by nlinarith [sq_nonneg t] : t^4≤(1:ℝ))]
    norm_num

theorem short_low_fourier_weighted_norm (x : Fin 7 → ℂ) :
    (∑ a : Fin 15, max 1 ((shortHeadFrequency a:ℝ)^4)*‖shortLowFourierCoordinates x a‖^2) ≤
      (7/6:ℝ)*(∑ k : Fin 7, ‖x k‖^2) := by
  have hh := short_low_weighted_embedding_norm x
  have heq (a : Fin 15) :
      ‖((max (1:ℝ) ((shortHeadFrequency a:ℝ)^2):ℝ):ℂ)*shortLowFourierCoordinates x a‖^2 =
      max 1 ((shortHeadFrequency a:ℝ)^4)*‖shortLowFourierCoordinates x a‖^2 := by
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,short_max_fourth_eq_square]
  change (∑ a : Fin 15, ‖((max (1:ℝ) ((shortHeadFrequency a:ℝ)^2):ℝ):ℂ)*
    shortLowFourierCoordinates x a‖^2) ≤ _ at hh
  simpa only [heq] using hh

theorem short_high_fourier_weighted_norm (n : ℤ) (hn : 4 ≤ n.natAbs) (y : ℂ) :
    max 1 ((2*(n:ℝ))^4)*‖y/(((2*(n:ℝ))^2:ℝ):ℂ)‖^2 = ‖y‖^2 := by
  have hd := short_half_square_pos n (by omega)
  have h1 := short_half_square_one_le n (by omega)
  have hn0 : (n:ℝ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  rw [max_eq_right (by nlinarith : (1:ℝ) ≤ (2*(n:ℝ))^4),norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hd,div_pow]
  field_simp [hn0]

theorem short_embedded_fourier_norm (I : Finset ℤ) (hI : ∀ n ∈ I, 4 ≤ n.natAbs)
    (x : Fin 7 → ℂ) (y : ℤ → ℂ) :
    (∑ a : Fin 15, max 1 ((shortHeadFrequency a:ℝ)^4)*‖shortLowFourierCoordinates x a‖^2) +
    (∑ n ∈ I, max 1 ((2*(n:ℝ))^4)*‖y n/(((2*(n:ℝ))^2:ℝ):ℂ)‖^2) ≤
      (7/6:ℝ)*((∑ k : Fin 7, ‖x k‖^2)+(∑ n ∈ I, ‖y n‖^2)) := by
  have hl := short_low_fourier_weighted_norm x
  have hh : (∑ n ∈ I, max 1 ((2*(n:ℝ))^4)*‖y n/(((2*(n:ℝ))^2:ℝ):ℂ)‖^2) = ∑ n ∈ I, ‖y n‖^2 := by
    exact sum_congr rfl (fun n hn => short_high_fourier_weighted_norm n (hI n hn) (y n))
  rw [hh]
  have hY : (0:ℝ) ≤ ∑ n ∈ I, ‖y n‖^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem short_embedded_kernel_energy (j : Fin 5) (I : Finset ℤ)
    (hI : ∀ n ∈ I, 4 ≤ n.natAbs) (x : Fin 7 → ℂ) (y : ℤ → ℂ) :
    (∑ a : Fin 15, ∑ b : Fin 15, conj (shortLowFourierCoordinates x a)*
      (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j
        ((a.val:ℤ)-7) ((b.val:ℤ)-7):ℂ)*shortLowFourierCoordinates x b).re +
    2*(∑ a : Fin 15, ∑ n ∈ I, conj (shortLowFourierCoordinates x a)*
      (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j ((a.val:ℤ)-7) n:ℂ)*
        (y n/(((2*(n:ℝ))^2:ℝ):ℂ))).re +
    (∑ n ∈ I, ∑ m ∈ I, conj (y n/(((2*(n:ℝ))^2:ℝ):ℂ))*
      (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j n m:ℂ)*
        (y m/(((2*(m:ℝ))^2:ℝ):ℂ))).re ≤
      -(1/100:ℝ)*((∑ i : Fin 7, ‖x i‖^2)+(∑ n ∈ I, ‖y n‖^2)) := by
  rw [short_embedded_low_kernel,short_embedded_cross_kernel,short_embedded_high_kernel]
  exact short_schur_polynomial_energy j I hI x y

end Lemniscate.CoarseArithmetic
