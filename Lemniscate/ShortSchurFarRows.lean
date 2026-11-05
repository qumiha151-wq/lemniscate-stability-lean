import Lemniscate.ShortSchurAllModeBounds

namespace Lemniscate.CoarseArithmetic
open Finset

theorem short_far_high_diagonal (j : Fin 5) (n : ℤ) (hn : 15 ≤ n.natAbs) :
    shortHighEntry j n n ≤
      -4*(rlo:ℝ)^2*(1-1/60:ℝ)^4+45*(rhi:ℝ)*(1+1/60:ℝ)^2/900 := by
  rw [short_high_entry_raw j n n (by omega) (by omega)]
  have hd := short_half_square_pos n (by omega)
  rw [div_le_iff₀ (mul_pos hd hd)]
  have hh := short_actual_raw_diagonal_bound j n hn
  change shortRawBernsteinEntry lemniscateFrequencySquared shortActualCoefficient j n n ≤ _ at hh
  exact hh.trans_eq (by ring)

theorem short_far_head_row (j : Fin 5) (n : ℤ) (hn : 15 ≤ n.natAbs)
    (I : Finset ℤ) (hI : ∀ m ∈ I, 4 ≤ m.natAbs ∧ m.natAbs ≤ 7) :
    (∑ m ∈ I, |shortHighEntry j n m|) ≤ 8*10^6*shortOutsideEnvelope n.natAbs := by
  let S : Finset ℤ := {-7,-6,-5,-4,4,5,6,7}
  have hsubset : I ⊆ S := by
    intro m hm
    have hm' := hI m hm
    simp only [S,mem_insert,mem_singleton]
    omega
  have hcard : I.card ≤ 8 := (card_le_card hsubset).trans_eq (by decide)
  have hE := short_outside_envelope_nonneg n.natAbs
  calc
    _ ≤ ∑ _m ∈ I, 10^6*shortOutsideEnvelope n.natAbs := by
      apply sum_le_sum
      intro m hm
      rw [short_high_entry_symmetric]
      exact short_high_head_outside_bound j m n (by have := hI m hm; omega) (hI m hm).2 hn
    _ = (I.card:ℝ)*(10^6*shortOutsideEnvelope n.natAbs) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hcard' : (I.card:ℝ) ≤ 8 := by exact_mod_cast hcard
      nlinarith

theorem short_far_raw_row (j : Fin 5) (n : ℤ) (hn : 15 ≤ n.natAbs)
    (I : Finset ℤ) (hI : ∀ m ∈ I, 8 ≤ m.natAbs) :
    (∑ m ∈ I, if m=n then 0 else |shortHighEntry j n m|) ≤
      2*(shortHighOffCoefficient:ℝ)*(moment 1 qb:ℝ) := by
  have hC : 0 ≤ (shortHighOffCoefficient:ℝ) := by norm_num [shortHighOffCoefficient,rhi,H,qb]
  have ht := short_finite_translated_geometric_tail qb (by norm_num [qb])
    (by norm_num [qb]) I n 0 (fun _ _ => Nat.zero_le _)
  calc
    _ ≤ ∑ m ∈ I, (shortHighOffCoefficient:ℝ)*((m-n).natAbs:ℝ)*(qb:ℝ)^(m-n).natAbs := by
      apply sum_le_sum
      intro m hm
      by_cases hmn : m=n
      · simp only [if_pos hmn,hmn,sub_self,Int.natAbs_zero,Nat.cast_zero,mul_zero,zero_mul]
        exact le_refl _
      · rw [if_neg hmn,short_high_entry_raw j n m (by omega) (hI m hm)]
        have habs : (n-m).natAbs = (m-n).natAbs := by rw [← Int.natAbs_neg (n-m),neg_sub]
        simpa only [habs] using short_high_raw_off_diagonal_bound j n m (Ne.symm hmn)
          (by omega) (by have := hI m hm; omega)
    _ = (shortHighOffCoefficient:ℝ)*(∑ m ∈ I, ((m-n).natAbs:ℝ)*(qb:ℝ)^(m-n).natAbs) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m _
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left ht hC
      have heq : (tail1 qb 0:ℝ) = (moment 1 qb:ℝ) := by norm_num [tail1,moment]
      rw [heq] at hh
      nlinarith

theorem short_far_high_row (j : Fin 5) (n : ℤ) (hn : 15 ≤ n.natAbs)
    (I : Finset ℤ) (hI : ∀ m ∈ I, 4 ≤ m.natAbs) :
    shortHighEntry j n n + (∑ m ∈ I, if m=n then 0 else |shortHighEntry j n m|) ≤ -(5/4:ℝ) := by
  let A := I.filter (fun m => m.natAbs ≤ 7)
  let B := I.filter (fun m => ¬m.natAbs ≤ 7)
  have hA : ∀ m ∈ A, 4 ≤ m.natAbs ∧ m.natAbs ≤ 7 := by
    intro m hm
    exact ⟨hI m (mem_filter.mp hm).1,(mem_filter.mp hm).2⟩
  have hB : ∀ m ∈ B, 8 ≤ m.natAbs := by
    intro m hm
    have := (mem_filter.mp hm).2
    omega
  have ha := short_far_head_row j n hn A hA
  have ha' : (∑ m ∈ A, if m=n then 0 else |shortHighEntry j n m|) ≤
      8*10^6*shortOutsideEnvelope n.natAbs := by
    convert ha using 1
    apply sum_congr rfl
    intro m hm
    exact if_neg (by have := (hA m hm).2; intro he; subst m; omega)
  have hb := short_far_raw_row j n hn B hB
  have hd := short_far_high_diagonal j n hn
  have he := short_outside_envelope_max n.natAbs hn
  have hnum : ((shortRawHighRow+shortFiniteRankHighTail:ℚ):ℝ) < -(5/4:ℝ) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr short_high_tail_arithmetic.2.2
    simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat] using hh
  have hsum := sum_filter_add_sum_filter_not I (fun m => m.natAbs ≤ 7)
    (fun m => if m=n then 0 else |shortHighEntry j n m|)
  change (∑ m ∈ A, _) + (∑ m ∈ B, _) = _ at hsum
  rw [← hsum]
  have hconst : ((shortRawHighRow+shortFiniteRankHighTail:ℚ):ℝ) =
      (-4*(rlo:ℝ)^2*(1-1/60:ℝ)^4+45*(rhi:ℝ)*(1+1/60:ℝ)^2/900) +
      2*(shortHighOffCoefficient:ℝ)*(moment 1 qb:ℝ) + 8*10^6*(22*(H:ℝ)*(qb:ℝ)^8) := by
    push_cast [shortRawHighRow,shortFiniteRankHighTail]
    ring
  rw [hconst] at hnum
  linarith

theorem short_all_high_row (j : Fin 5) (n : ℤ) (I : Finset ℤ)
    (hn : 4 ≤ n.natAbs) (hI : ∀ m ∈ I, 4 ≤ m.natAbs) :
    shortHighEntry j n n + (∑ m ∈ I, if m=n then 0 else |shortHighEntry j n m|) ≤ -(5/4:ℝ) := by
  by_cases hn14 : n.natAbs ≤ 14
  · exact short_small_high_row j n I hn hn14 hI
  · exact short_far_high_row j n (by omega) I hI

end Lemniscate.CoarseArithmetic
