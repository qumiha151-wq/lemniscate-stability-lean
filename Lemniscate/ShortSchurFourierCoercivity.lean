import Lemniscate.ShortSchurKernelEnergy

namespace Lemniscate.CoarseArithmetic
open Finset Complex
open scoped ComplexConjugate

private def lowHalf (i : Fin 15) : ℤ := (i.val:ℤ)-7

private def lowPresent (J : Finset ℤ) (i : Fin 15) : Prop :=
  lowHalf i ∈ J ∧ (lowHalf i).natAbs ≤ 3

private instance (J : Finset ℤ) (i : Fin 15) : Decidable (lowPresent J i) := by
  unfold lowPresent
  infer_instance

private noncomputable def lowCoefficient (J : Finset ℤ) (a : ℤ → ℂ) (i : Fin 15) : ℂ :=
  if lowPresent J i then a (lowHalf i) else 0

private theorem low_filter_sum {β : Type*} [AddCommMonoid β]
    (J : Finset ℤ) (f : ℤ → β) :
    (∑ i : Fin 15, if lowPresent J i then f (lowHalf i) else 0) =
      ∑ n ∈ J.filter (fun n => n.natAbs≤3), f n := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => lowHalf i)
  · intro i hi
    exact mem_filter.mpr (mem_filter.mp hi).2
  · intro i _ k _ hik
    apply Fin.ext
    dsimp only [lowHalf] at hik
    omega
  · intro n hn
    have hn' := mem_filter.mp hn
    let i : Fin 15 := ⟨(n+7).toNat,by omega⟩
    have hi : lowHalf i = n := by dsimp only [lowHalf,i]; omega
    refine ⟨i,?_,hi⟩
    apply mem_filter.mpr
    exact ⟨mem_univ _,by simpa only [lowPresent,hi] using hn'⟩
  · intro _ _; rfl

private theorem coefficient_sum_split (J : Finset ℤ) (a f : ℤ → ℂ) :
    (∑ n ∈ J, a n*f n) =
      (∑ i : Fin 15, lowCoefficient J a i*f (lowHalf i)) +
      (∑ n ∈ J.filter (fun n => 4≤n.natAbs), a n*f n) := by
  classical
  have hl : (∑ i : Fin 15, lowCoefficient J a i*f (lowHalf i)) =
      ∑ n ∈ J.filter (fun n => n.natAbs≤3), a n*f n := by
    have hh := low_filter_sum J (fun n => a n*f n)
    convert hh using 1
    apply sum_congr rfl
    intro i _
    by_cases hi : lowPresent J i <;> simp only [lowCoefficient,hi,ite_true,ite_false,zero_mul]
  have heq : J.filter (fun n => ¬n.natAbs≤3) = J.filter (fun n => 4≤n.natAbs) := by
    ext n
    simp only [mem_filter,not_le,Nat.lt_iff_add_one_le]
  rw [hl,← heq]
  exact (sum_filter_add_sum_filter_not J (fun n => n.natAbs≤3) _).symm

private theorem conjugate_sum_split (J : Finset ℤ) (a f : ℤ → ℂ) :
    (∑ n ∈ J, conj (a n)*f n) =
      (∑ i : Fin 15, conj (lowCoefficient J a i)*f (lowHalf i)) +
      (∑ n ∈ J.filter (fun n => 4≤n.natAbs), conj (a n)*f n) := by
  have hh := coefficient_sum_split J (fun n => conj (a n)) f
  have heq (i : Fin 15) : lowCoefficient J (fun n => conj (a n)) i = conj (lowCoefficient J a i) := by
    by_cases hi : lowPresent J i <;> simp only [lowCoefficient,hi,ite_true,ite_false,map_zero]
  simpa only [heq] using hh

private theorem coefficient_weight_split (J : Finset ℤ) (a : ℤ → ℂ) :
    (∑ n ∈ J, max 1 ((2*(n:ℝ))^4)*‖a n‖^2) =
      (∑ i : Fin 15, max 1 ((shortHeadFrequency i:ℝ)^4)*‖lowCoefficient J a i‖^2) +
      (∑ n ∈ J.filter (fun n => 4≤n.natAbs), max 1 ((2*(n:ℝ))^4)*‖a n‖^2) := by
  classical
  have hfreq (i : Fin 15) : (shortHeadFrequency i:ℝ) = 2*(lowHalf i:ℝ) := by
    dsimp only [shortHeadFrequency,lowHalf]
    push_cast
    ring
  have hl := low_filter_sum J (fun n => max 1 ((2*(n:ℝ))^4)*‖a n‖^2)
  have hl' : (∑ i : Fin 15, max 1 ((shortHeadFrequency i:ℝ)^4)*‖lowCoefficient J a i‖^2) =
      ∑ n ∈ J.filter (fun n => n.natAbs≤3), max 1 ((2*(n:ℝ))^4)*‖a n‖^2 := by
    convert hl using 1
    apply sum_congr rfl
    intro i _
    rw [hfreq]
    by_cases hi : lowPresent J i <;>
      simp only [lowCoefficient,hi,ite_true,ite_false,norm_zero,zero_pow (by decide : 2≠0),mul_zero]
  have heq : J.filter (fun n => ¬n.natAbs≤3) = J.filter (fun n => 4≤n.natAbs) := by
    ext n
    simp only [mem_filter,not_le,Nat.lt_iff_add_one_le]
  rw [hl',← heq]
  exact (sum_filter_add_sum_filter_not J (fun n => n.natAbs≤3) _).symm

private theorem quadratic_sum_split (J : Finset ℤ) (a : ℤ → ℂ) (K : ℤ → ℤ → ℝ)
    (hsym : ∀ n m, K n m = K m n) :
    (∑ n ∈ J, ∑ m ∈ J, conj (a n)*(K n m:ℂ)*a m).re =
      (∑ i : Fin 15, ∑ k : Fin 15,
        conj (lowCoefficient J a i)*(K (lowHalf i) (lowHalf k):ℂ)*lowCoefficient J a k).re +
      2*(∑ i : Fin 15, ∑ n ∈ J.filter (fun n => 4≤n.natAbs),
        conj (lowCoefficient J a i)*(K (lowHalf i) n:ℂ)*a n).re +
      (∑ n ∈ J.filter (fun n => 4≤n.natAbs), ∑ m ∈ J.filter (fun n => 4≤n.natAbs),
        conj (a n)*(K n m:ℂ)*a m).re := by
  have hinner (n : ℤ) : (∑ m ∈ J, (K n m:ℂ)*a m) =
      (∑ i : Fin 15, (K n (lowHalf i):ℂ)*lowCoefficient J a i) +
      (∑ m ∈ J.filter (fun n => 4≤n.natAbs), (K n m:ℂ)*a m) := by
    simpa only [mul_comm] using coefficient_sum_split J a (fun m => (K n m:ℂ))
  have hraw : (∑ n ∈ J, ∑ m ∈ J, conj (a n)*(K n m:ℂ)*a m) =
      (∑ i : Fin 15, ∑ k : Fin 15,
        conj (lowCoefficient J a i)*(K (lowHalf i) (lowHalf k):ℂ)*lowCoefficient J a k) +
      (∑ i : Fin 15, ∑ n ∈ J.filter (fun n => 4≤n.natAbs),
        conj (lowCoefficient J a i)*(K (lowHalf i) n:ℂ)*a n) +
      (∑ n ∈ J.filter (fun n => 4≤n.natAbs), ∑ i : Fin 15,
        conj (a n)*(K n (lowHalf i):ℂ)*lowCoefficient J a i) +
      (∑ n ∈ J.filter (fun n => 4≤n.natAbs), ∑ m ∈ J.filter (fun n => 4≤n.natAbs),
        conj (a n)*(K n m:ℂ)*a m) := by
    calc
      _ = ∑ n ∈ J, conj (a n)*(∑ m ∈ J, (K n m:ℂ)*a m) := by
        simp only [mul_sum,mul_assoc]
      _ = _ := by
        rw [conjugate_sum_split]
        simp_rw [hinner,mul_add,mul_sum,sum_add_distrib]
        simp only [mul_assoc]
        ring
  have hreverse : (∑ n ∈ J.filter (fun n => 4≤n.natAbs), ∑ i : Fin 15,
        conj (a n)*(K n (lowHalf i):ℂ)*lowCoefficient J a i) =
      conj (∑ i : Fin 15, ∑ n ∈ J.filter (fun n => 4≤n.natAbs),
        conj (lowCoefficient J a i)*(K (lowHalf i) n:ℂ)*a n) := by
    rw [Finset.sum_comm]
    simp only [map_sum,map_mul,Complex.conj_conj,Complex.conj_ofReal]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro n _
    rw [hsym n (lowHalf i)]
    ring
  rw [hraw,hreverse]
  simp only [Complex.add_re,Complex.conj_re]
  ring

theorem short_kernel_polynomial_coercivity (j : Fin 5) (J : Finset ℤ) (a : ℤ → ℂ) :
    (∑ n ∈ J, ∑ m ∈ J, conj (a n)*
      (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j n m:ℂ)*a m).re ≤
      -(3/350:ℝ)*(∑ n ∈ J, max 1 ((2*(n:ℝ))^4)*‖a n‖^2) := by
  classical
  let I := J.filter (fun n => 4≤n.natAbs)
  have hI : ∀ n ∈ I, 4≤n.natAbs := fun n hn => (mem_filter.mp hn).2
  have hq : ∀ i, i.val < 4 ∨ 10 < i.val → lowCoefficient J a i = 0 := by
    intro i hi
    have hn : ¬lowPresent J i := by
      intro h
      have hh := h.2
      dsimp only [lowHalf] at hh
      omega
    simp only [lowCoefficient,if_neg hn]
  obtain ⟨x,hx⟩ := short_low_embedding_surjective (lowCoefficient J a) hq
  have hx' : ∀ i, shortLowFourierCoordinates x i = lowCoefficient J a i := hx
  let y (n : ℤ) : ℂ := (((2*(n:ℝ))^2:ℝ):ℂ)*a n
  have hy (n : ℤ) (hn : n ∈ I) : y n/(((2*(n:ℝ))^2:ℝ):ℂ) = a n := by
    have hd := short_half_square_pos n (by have := hI n hn; omega)
    have hd0 : (((2*(n:ℝ))^2:ℝ):ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
    exact mul_div_cancel_left₀ _ hd0
  have he := short_embedded_kernel_energy j I hI x y
  have hv := short_embedded_fourier_norm I hI x y
  have hc : (∑ i : Fin 15, ∑ n ∈ I, conj (shortLowFourierCoordinates x i)*
      (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j (lowHalf i) n:ℂ)*
        (y n/(((2*(n:ℝ))^2:ℝ):ℂ))) =
      ∑ i : Fin 15, ∑ n ∈ I, conj (lowCoefficient J a i)*
        (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j (lowHalf i) n:ℂ)*a n := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro n hn
    rw [hx',hy n hn]
  have hh : (∑ n ∈ I, ∑ m ∈ I, conj (y n/(((2*(n:ℝ))^2:ℝ):ℂ))*
      (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j n m:ℂ)*
        (y m/(((2*(m:ℝ))^2:ℝ):ℂ))) =
      ∑ n ∈ I, ∑ m ∈ I, conj (a n)*
        (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j n m:ℂ)*a m := by
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    rw [hy n hn,hy m hm]
  change _ + 2*(∑ i : Fin 15, ∑ n ∈ I, conj (shortLowFourierCoordinates x i)*
    (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j (lowHalf i) n:ℂ)*
      (y n/(((2*(n:ℝ))^2:ℝ):ℂ))).re + _ ≤ _ at he
  rw [hc,hh] at he
  simp only [hx'] at he hv
  have hsplit := quadratic_sum_split J a
    (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j)
    (short_bernstein_kernel_symmetric _ _ j)
  change _ = _ + 2*(∑ i : Fin 15, ∑ n ∈ I, (_ : ℂ)).re +
    (∑ n ∈ I, ∑ m ∈ I, (_ : ℂ)).re at hsplit
  dsimp only [lowHalf] at he hsplit
  rw [← hsplit] at he
  have hvh : (∑ n ∈ I, max 1 ((2*(n:ℝ))^4)*‖y n/(((2*(n:ℝ))^2:ℝ):ℂ)‖^2) =
      ∑ n ∈ I, max 1 ((2*(n:ℝ))^4)*‖a n‖^2 := by
    apply sum_congr rfl
    intro n hn
    rw [hy n hn]
  rw [hvh] at hv
  have hweight := coefficient_weight_split J a
  change _ = _ + (∑ n ∈ I, _) at hweight
  rw [← hweight] at hv
  linarith

end Lemniscate.CoarseArithmetic
