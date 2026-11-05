import Lemniscate.ShortSchurExteriorEstimates
import Lemniscate.ShortSchurFiniteBounds
import Lemniscate.ShortSchurGeometricTails
import Lemniscate.ShortSchurDiagonalBounds

/-! The finite certificate and the complete geometric tails control arbitrary
finite sets of high Fourier modes. No Fourier cutoff is an assumption. -/
namespace Lemniscate.CoarseArithmetic
open Finset

theorem short_high_half_frequency_injective : Function.Injective shortHighHalfFrequency := by
  intro i k hik
  unfold shortHighHalfFrequency at hik
  split_ifs at hik <;> apply Fin.ext <;> omega

theorem short_high_half_frequency_surjective (n : ℤ)
    (hn : 4 ≤ n.natAbs) (hn14 : n.natAbs ≤ 14) :
    ∃ k : Fin 22, shortHighHalfFrequency k = n := by
  by_cases hneg : n < 0
  · refine ⟨⟨(n+14).toNat,by omega⟩,?_⟩
    unfold shortHighHalfFrequency
    dsimp only
    rw [if_pos (by omega)]
    omega
  · refine ⟨⟨(n+7).toNat,by omega⟩,?_⟩
    unfold shortHighHalfFrequency
    dsimp only
    rw [if_neg (by omega)]
    omega

theorem short_sum_finite_high_le (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (I : Finset ℤ) (hI : ∀ n ∈ I, 4 ≤ n.natAbs ∧ n.natAbs ≤ 14) :
    (∑ n ∈ I, f n) ≤ ∑ k : Fin 22, f (shortHighHalfFrequency k) := by
  have hsubset : I ⊆ univ.image shortHighHalfFrequency := by
    intro n hn
    obtain ⟨k,hk⟩ := short_high_half_frequency_surjective n (hI n hn).1 (hI n hn).2
    exact mem_image.mpr ⟨k,mem_univ _,hk⟩
  calc
    _ ≤ ∑ n ∈ univ.image shortHighHalfFrequency, f n :=
      sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => hf n)
    _ = _ := sum_image (fun i _ k _ hik => short_high_half_frequency_injective hik)

theorem short_cross_square_tail (j : Fin 5) (I : Finset ℤ)
    (hI : ∀ n ∈ I, 15 ≤ n.natAbs) :
    (∑ i : Fin 7, ∑ n ∈ I, |shortCrossEntry j i n|^2) ≤ (shortCrossTailSquare:ℝ) := by
  have htail := (short_finite_outer_envelope_tails I hI).2
  have hone (i : Fin 7) :
      (∑ n ∈ I, |shortCrossEntry j i n|^2) ≤
        10^12*(∑ n ∈ I, shortOutsideEnvelope n.natAbs^2) := by
    calc
      _ ≤ ∑ n ∈ I, (10^6*shortOutsideEnvelope n.natAbs)^2 :=
        sum_le_sum (fun n hn => pow_le_pow_left₀ (abs_nonneg _)
          (short_cross_outside_bound j i n (hI n hn)) 2)
      _ = _ := by simp only [mul_pow, mul_sum]; norm_num
  have hsum := sum_le_sum (s := (univ:Finset (Fin 7))) (fun i _ => hone i)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  change (∑ n ∈ I, shortOutsideEnvelope n.natAbs^2) ≤ _ at htail
  norm_num at hsum htail
  simp only [sq_abs]
  nlinarith

theorem short_all_cross_square (j : Fin 5) (I : Finset ℤ)
    (hI : ∀ n ∈ I, 4 ≤ n.natAbs) :
    (∑ i : Fin 7, ∑ n ∈ I, |shortCrossEntry j i n|^2) ≤ (1/16:ℝ) := by
  let A := I.filter (fun n => n.natAbs ≤ 14)
  let B := I.filter (fun n => ¬n.natAbs ≤ 14)
  have hA : ∀ n ∈ A, 4 ≤ n.natAbs ∧ n.natAbs ≤ 14 := by
    intro n hn
    exact ⟨hI n (mem_filter.mp hn).1,(mem_filter.mp hn).2⟩
  have hB : ∀ n ∈ B, 15 ≤ n.natAbs := by
    intro n hn
    have := (mem_filter.mp hn).2
    omega
  have hsmall : (∑ i : Fin 7, ∑ n ∈ A, |shortCrossEntry j i n|^2) ≤
      ∑ i : Fin 7, ∑ k : Fin 22, |shortCrossEntry j i (shortHighHalfFrequency k)|^2 := by
    exact sum_le_sum (fun i _ => short_sum_finite_high_le _ (fun _ => sq_nonneg _) A hA)
  have hsplit : (∑ i : Fin 7, ∑ n ∈ I, |shortCrossEntry j i n|^2) =
      (∑ i : Fin 7, ∑ n ∈ A, |shortCrossEntry j i n|^2) +
      (∑ i : Fin 7, ∑ n ∈ B, |shortCrossEntry j i n|^2) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    exact (sum_filter_add_sum_filter_not I (fun n => n.natAbs ≤ 14) _).symm
  rw [hsplit]
  exact (add_le_add hsmall (short_cross_square_tail j B hB)).trans (short_finite_cross_square j)

theorem short_high_far_columns (j : Fin 5) (n : ℤ) (I : Finset ℤ)
    (hn : 4 ≤ n.natAbs) (hn14 : n.natAbs ≤ 14)
    (hI : ∀ m ∈ I, 15 ≤ m.natAbs) :
    (∑ m ∈ I, |shortHighEntry j n m|) ≤
      if n.natAbs ≤ 7 then (shortInsideRowTail:ℝ) else
        (2*shortHighOffCoefficient*tail1 qb (15-n.natAbs):ℚ) := by
  by_cases hn7 : n.natAbs ≤ 7
  · rw [if_pos hn7]
    have ht := (short_finite_outer_envelope_tails I hI).1
    change (∑ m ∈ I, shortOutsideEnvelope m.natAbs) ≤ _ at ht
    calc
      _ ≤ ∑ m ∈ I, 10^6*shortOutsideEnvelope m.natAbs :=
        sum_le_sum (fun m hm => short_high_head_outside_bound j n m (by omega) hn7 (hI m hm))
      _ = 10^6*(∑ m ∈ I, shortOutsideEnvelope m.natAbs) := by rw [mul_sum]
      _ ≤ _ := by linarith
  · rw [if_neg hn7]
    have hdist (m : ℤ) (hm : m ∈ I) : 15-n.natAbs ≤ (m-n).natAbs := by
      have htriangle := Int.natAbs_add_le (m-n) n
      rw [sub_add_cancel] at htriangle
      have := hI m hm
      omega
    have ht := short_finite_translated_geometric_tail qb (by norm_num [qb])
      (by norm_num [qb]) I n (15-n.natAbs) hdist
    have hC : 0 ≤ (shortHighOffCoefficient:ℝ) := by norm_num [shortHighOffCoefficient,rhi,H,qb]
    calc
      _ ≤ ∑ m ∈ I, (shortHighOffCoefficient:ℝ)*((m-n).natAbs:ℝ)*(qb:ℝ)^(m-n).natAbs := by
        apply sum_le_sum
        intro m hm
        rw [short_high_entry_raw j n m (by omega) (by have := hI m hm; omega)]
        have hnm : n ≠ m := by have := hI m hm; intro he; subst m; omega
        have habs : (n-m).natAbs = (m-n).natAbs := by rw [← Int.natAbs_neg (n-m),neg_sub]
        simpa only [habs] using short_high_raw_off_diagonal_bound j n m hnm hn (by have := hI m hm; omega)
      _ = (shortHighOffCoefficient:ℝ)*(∑ m ∈ I, ((m-n).natAbs:ℝ)*(qb:ℝ)^(m-n).natAbs) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro m _
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left ht hC
        simp only [Rat.cast_mul,Rat.cast_ofNat]
        nlinarith only [hh]

theorem short_small_high_row (j : Fin 5) (n : ℤ) (I : Finset ℤ)
    (hn : 4 ≤ n.natAbs) (hn14 : n.natAbs ≤ 14)
    (hI : ∀ m ∈ I, 4 ≤ m.natAbs) :
    shortHighEntry j n n + (∑ m ∈ I, if m=n then 0 else |shortHighEntry j n m|) ≤ -(5/4:ℝ) := by
  obtain ⟨k,hk⟩ := short_high_half_frequency_surjective n hn hn14
  let A := I.filter (fun m => m.natAbs ≤ 14)
  let B := I.filter (fun m => ¬m.natAbs ≤ 14)
  have hA : ∀ m ∈ A, 4 ≤ m.natAbs ∧ m.natAbs ≤ 14 := by
    intro m hm
    exact ⟨hI m (mem_filter.mp hm).1,(mem_filter.mp hm).2⟩
  have hB : ∀ m ∈ B, 15 ≤ m.natAbs := by
    intro m hm
    have := (mem_filter.mp hm).2
    omega
  have hsmall := short_sum_finite_high_le (fun m => if m=n then 0 else |shortHighEntry j n m|)
    (fun m => by split_ifs <;> positivity) A hA
  have hlarge := short_high_far_columns j n B hn hn14 hB
  have hlarge' : (∑ m ∈ B, if m=n then 0 else |shortHighEntry j n m|) ≤
      (shortFiniteHighTail k:ℝ) := by
    have heq : (∑ m ∈ B, if m=n then 0 else |shortHighEntry j n m|) = ∑ m ∈ B, |shortHighEntry j n m| := by
      apply sum_congr rfl
      intro m hm
      rw [if_neg (by have := hB m hm; intro he; subst m; omega)]
    rw [heq]
    by_cases h7 : n.natAbs ≤ 7
    · simpa only [shortFiniteHighTail,hk,if_pos h7] using hlarge
    · simpa only [shortFiniteHighTail,hk,if_neg h7,Rat.cast_mul,Rat.cast_ofNat] using hlarge
  have hfinite := short_finite_high_row j k
  have hrewrite : (∑ z : Fin 22, if shortHighHalfFrequency z=n then 0 else |shortHighEntry j n (shortHighHalfFrequency z)|) =
      ∑ z : Fin 22, if z=k then 0 else |shortHighEntry j (shortHighHalfFrequency k) (shortHighHalfFrequency z)| := by
    apply sum_congr rfl
    intro z _
    rw [← hk]
    simp only [short_high_half_frequency_injective.eq_iff]
  rw [hrewrite] at hsmall
  rw [← hk] at hlarge'
  have hsplit := sum_filter_add_sum_filter_not I (fun m => m.natAbs ≤ 14)
    (fun m => if m=n then 0 else |shortHighEntry j n m|)
  change (∑ m ∈ A, _) + (∑ m ∈ B, _) = _ at hsplit
  rw [← hsplit]
  rw [← hk] at hsmall ⊢
  linarith

end Lemniscate.CoarseArithmetic
