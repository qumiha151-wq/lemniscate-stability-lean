import Lemniscate.EvenCouplingEntryBounds
import Lemniscate.PeriodicEvenTailSum

/-! The complete high-frequency rows of the actual symmetric Bloch
coefficients, with the same weights as the finite even energy estimate. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

def evenCouplingRowUpper (m : ℤ) : ℚ :=
  2*36*(if 12 ≤ m.natAbs then 3/8 else 15000)*tail2 (qb^2) (16-m.natAbs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_baseline_row_certificate :
    (∑ i : Fin 31, evenCouplingRowUpper ((i.val:ℤ)-15)) ≤ evenAnalyticBaseUpper := by
  decide +kernel

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleSymmetricHighRow (h h₁ h₂ : C(AddCircle T, ℂ)) (m n : ℤ) : ℝ :=
  if Even n ∧ 32 ≤ |(n:ℝ)| then
    ∑ j : Fin 3,
      ‖fourierCoeff (circleBlochSymmetricCoefficient T h h₁ h₂ j (circleFourierH4 T (2*m))) n‖^2 /
        ((evenModePenalty (2*m):ℝ)*(n:ℝ)^4)
  else 0

theorem circle_symmetric_high_row_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25) (m : ℤ) (hm : m.natAbs ≤ 15) :
    Summable (circleSymmetricHighRow T h h₁ h₂ m) ∧
      (∑' n : ℤ, circleSymmetricHighRow T h h₁ h₂ m n) ≤ (evenCouplingRowUpper m:ℝ) := by
  classical
  let F := circleSymmetricHighRow T h h₁ h₂ m
  let W : ℝ := if 12 ≤ m.natAbs then 3/8 else 15000
  have hW : 0 ≤ W := by dsimp only [W]; split_ifs <;> norm_num
  have hδ : 0 < (evenModePenalty (2*m):ℝ) := Rat.cast_pos.mpr
    (lt_of_lt_of_le (by norm_num : (0:ℚ) < 1/16) (even_mode_penalty_lower (2*m)))
  have hn (n : ℤ) : 0 ≤ F n := by
    dsimp only [F,circleSymmetricHighRow]
    split_ifs
    · apply Finset.sum_nonneg
      intro j _
      positivity
    · exact le_rfl
  have he (k : ℤ) : F (2*k) = if 16 ≤ k.natAbs then
      ∑ j : Fin 3,
        ‖fourierCoeff (circleBlochSymmetricCoefficient T h h₁ h₂ j (circleFourierH4 T (2*m))) (2*k)‖^2 /
          ((evenModePenalty (2*m):ℝ)*(2*(k:ℝ))^4) else 0 := by
    simp only [F,circleSymmetricHighRow,show Even (2*k) from ⟨k,by ring⟩,true_and]
    simp only [even_high_frequency_iff]
    simp only [Int.cast_mul,Int.cast_ofNat]
  have hb (k : ℤ) : F (2*k) ≤ if 16 ≤ k.natAbs then
      (36*W)*((k.natAbs-m.natAbs:ℕ):ℝ)^2*((qb^2:ℚ):ℝ)^(k.natAbs-m.natAbs) else 0 := by
    rw [he]
    by_cases hk : 16 ≤ k.natAbs
    · rw [if_pos hk,if_pos hk]
      have hp : ‖fourierCoeff h (2*k-2*m)‖ ≤
          6*((k.natAbs-m.natAbs:ℕ):ℝ)*(qb:ℝ)^(k.natAbs-m.natAbs) := by
        simpa only [mul_sub] using circle_even_coefficient_distance_bound T h hs hc
          k m m.natAbs (by omega) le_rfl
      have hsq := pow_le_pow_left₀ (norm_nonneg (fourierCoeff h (2*k-2*m))) hp 2
      have hpow : ((qb:ℝ)^(k.natAbs-m.natAbs))^2 =
          ((qb^2:ℚ):ℝ)^(k.natAbs-m.natAbs) := by
        simp only [Rat.cast_pow,← pow_mul,Nat.mul_comm]
      have hsq' : ‖fourierCoeff h (2*k-2*m)‖^2 ≤
          36*((k.natAbs-m.natAbs:ℕ):ℝ)^2*((qb^2:ℚ):ℝ)^(k.natAbs-m.natAbs) := by
        calc
          _ ≤ (6*((k.natAbs-m.natAbs:ℕ):ℝ)*(qb:ℝ)^(k.natAbs-m.natAbs))^2 := hsq
          _ = _ := by rw [mul_pow,mul_pow,hpow]; ring
      calc
        _ ≤ W*‖fourierCoeff h (2*k-2*m)‖^2 :=
          circle_bloch_symmetric_entry_square_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr k m hk hm
        _ ≤ W*(36*((k.natAbs-m.natAbs:ℕ):ℝ)^2*((qb^2:ℚ):ℝ)^(k.natAbs-m.natAbs)) :=
          mul_le_mul_of_nonneg_left hsq' hW
        _ = _ := by ring
    · simp only [if_neg hk,le_refl]
  have hsum := even_high_geometric_sum (fun k => F (2*k)) (36*W) m.natAbs 16 (by omega) (by decide)
    (qb^2) (by norm_num [qb]) (fun k => hn (2*k)) hb
  have hodd (n : ℤ) (hn : ¬Even n) : F n = 0 := by
    simp only [F,circleSymmetricHighRow,hn,false_and,if_false]
  have hfull := even_frequency_sum F hodd hsum.1
  refine ⟨hfull.1,?_⟩
  rw [hfull.2]
  apply hsum.2.trans_eq
  dsimp only [evenCouplingRowUpper,W]
  by_cases hlarge : 12 ≤ m.natAbs <;>
    simp only [hlarge,if_true,if_false,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] <;> ring

theorem circle_symmetric_high_head_row (h h₁ h₂ : C(AddCircle T, ℂ)) (i : Fin 31) (n : ℤ) :
    circleSymmetricHighRow T h h₁ h₂ ((i.val:ℤ)-15) n =
      if Even n ∧ 32 ≤ |(n:ℝ)| then ∑ j : Fin 3,
        ‖fourierCoeff (circleBlochSymmetricCoefficient T h h₁ h₂ j
          (circleFourierH4 T (evenHeadFrequency i))) n‖^2/
            ((evenFactorPenalty i:ℝ)*(n:ℝ)^4) else 0 := by
  rw [even_factor_penalty_values i]
  have hfreq : evenHeadFrequency i = 2*((i.val:ℤ)-15) := by dsimp only [evenHeadFrequency]; ring
  rw [hfreq]
  rfl

theorem circle_symmetric_baseline_matrix_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25) :
    (∑ i : Fin 31, ∑' n : ℤ, if Even n ∧ 32 ≤ |(n:ℝ)| then
      ∑ j : Fin 3,
        ‖fourierCoeff (circleBlochSymmetricCoefficient T h h₁ h₂ j
          (circleFourierH4 T (evenHeadFrequency i))) n‖^2/
            ((evenFactorPenalty i:ℝ)*(n:ℝ)^4) else 0) < (1/9:ℝ) := by
  classical
  have hm (i : Fin 31) : ((i.val:ℤ)-15).natAbs ≤ 15 := by
    have hi := i.isLt
    have hb : (((i.val:ℤ)-15).natAbs:ℤ) ≤ 15 := by
      rw [Int.natCast_natAbs,abs_le]
      constructor <;> omega
    exact_mod_cast hb
  simp_rw [← circle_symmetric_high_head_row T h h₁ h₂]
  calc
    _ ≤ ∑ i : Fin 31, (evenCouplingRowUpper ((i.val:ℤ)-15):ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (circle_symmetric_high_row_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr _ (hm i)).2
    _ ≤ (evenAnalyticBaseUpper:ℝ) := by
      have hnum : ((∑ i : Fin 31, evenCouplingRowUpper ((i.val:ℤ)-15):ℚ):ℝ) ≤
          (evenAnalyticBaseUpper:ℝ) := Rat.cast_le.mpr even_baseline_row_certificate
      simpa only [Rat.cast_sum] using hnum
    _ < _ := by
      have hnum : (evenAnalyticBaseUpper:ℝ) < ((1/9:ℚ):ℝ) :=
        Rat.cast_lt.mpr even_analytic_coupling_constants.1
      norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hnum
      exact hnum

end Lemniscate
