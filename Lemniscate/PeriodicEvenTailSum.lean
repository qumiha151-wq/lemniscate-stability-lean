import Lemniscate.PeriodicLowTrialTail

/-! Sum the full two-sided geometric tail, and apply it to even high Fourier
coefficients. No finite truncation replaces the infinite sum. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

theorem even_high_frequency_iff (k : ℤ) :
    32 ≤ |((2*k:ℤ):ℝ)| ↔ 16 ≤ k.natAbs := by
  have hcast : (k.natAbs:ℝ) = |(k:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  rw [Int.cast_mul,Int.cast_ofNat,abs_mul,show |(2:ℝ)| = 2 by norm_num,← hcast]
  constructor <;> intro h
  · have h' : (16:ℝ) ≤ (k.natAbs:ℝ) := by linarith only [h]
    exact_mod_cast h'
  · have h' : (16:ℝ) ≤ (k.natAbs:ℝ) := by exact_mod_cast h
    linarith only [h']

theorem even_frequency_sum (F : ℤ → ℝ) (hF : ∀ n, ¬Even n → F n = 0)
    (hSum : Summable (fun k : ℤ => F (2*k))) :
    Summable F ∧ (∑' n, F n) = ∑' k, F (2*k) := by
  have hi : Function.Injective (fun k : ℤ => 2*k) := by
    intro a b hab
    exact mul_left_cancel₀ (by norm_num : (2:ℤ) ≠ 0) hab
  have hz (n : ℤ) (hn : n ∉ Set.range (fun k : ℤ => 2*k)) : F n = 0 := by
    apply hF n
    rintro ⟨k,hk⟩
    apply hn
    exact ⟨k,by linarith only [hk]⟩
  have h := (hi.hasSum_iff hz).mp hSum.hasSum
  exact ⟨h.summable,h.tsum_eq⟩

theorem even_high_geometric_sum (F : ℤ → ℝ) (C : ℝ)
    (a b : ℕ) (hab : a ≤ b) (hbpos : 0 < b)
    (z : ℚ) (hz : ‖(z:ℝ)‖ < 1)
    (hF : ∀ k, 0 ≤ F k)
    (hb : ∀ k, F k ≤ if b ≤ k.natAbs then
      C*((k.natAbs-a:ℕ):ℝ)^2*(z:ℝ)^(k.natAbs-a) else 0) :
    Summable F ∧ (∑' k, F k) ≤ 2*C*(tail2 z (b-a):ℝ) := by
  let G (n : ℕ) : ℝ := if b ≤ n then C*((n-a:ℕ):ℝ)^2*(z:ℝ)^(n-a) else 0
  have hshift : HasSum (fun n : ℕ => G (n+b)) (C*(tail2 z (b-a):ℝ)) := by
    have he : (fun n : ℕ => G (n+b)) =
        (fun n : ℕ => C*(((n+(b-a):ℕ):ℝ)^2*(z:ℝ)^(n+(b-a)))) := by
      funext n
      simp only [G,if_pos (by omega : b ≤ n+b),show n+b-a = n+(b-a) by omega]
      ring
    rw [he]
    exact (tail2_sound z hz (b-a)).mul_left C
  have hzero : (∑ n ∈ Finset.range b, G n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact if_neg (by have := Finset.mem_range.mp hn; omega)
  have hG : HasSum G (C*(tail2 z (b-a):ℝ)) := by
    apply (hasSum_nat_add_iff' b).mp
    simpa only [hzero,sub_zero] using hshift
  have hG' : HasSum (fun n : ℕ => G (n+1)) (C*(tail2 z (b-a):ℝ)) := by
    have h := (hasSum_nat_add_iff' 1).mpr hG
    simpa [G,show ¬b ≤ 0 by omega] using h
  have hp (n : ℕ) : F (n:ℤ) ≤ G n := by
    simpa only [Int.natAbs_natCast,G] using hb (n:ℤ)
  have hn (n : ℕ) : F (-((n:ℤ)+1)) ≤ G (n+1) := by
    simpa only [← Int.natCast_succ,Int.natAbs_neg,Int.natAbs_natCast,G] using hb (-((n:ℤ)+1))
  have hFp := Summable.of_nonneg_of_le (fun n : ℕ => hF (n:ℤ)) hp hG.summable
  have hFn := Summable.of_nonneg_of_le (fun n : ℕ => hF (-((n:ℤ)+1))) hn hG'.summable
  refine ⟨hFp.of_nat_of_neg_add_one hFn, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hFp hFn]
  have hsum := add_le_add (hFp.tsum_le_tsum hp hG.summable)
    (hFn.tsum_le_tsum hn hG'.summable)
  rw [hG.tsum_eq,hG'.tsum_eq] at hsum
  linarith only [hsum]

variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_high_square_of_geometric_bound (g : CircleL2 T)
    (hb : ∀ k : ℤ, 16 ≤ k.natAbs → ‖fourierCoeff g (2*k)‖ ≤
      1800*(2*(k:ℝ))^2*((k.natAbs-10:ℕ):ℝ)*(qb:ℝ)^(k.natAbs-10)) :
    (∑' n : ℤ, if Even n ∧ 32 ≤ |(n:ℝ)| then
      ‖fourierCoeff g n‖^2/(n:ℝ)^4 else 0) ≤ (1/8000:ℝ)^2 := by
  classical
  let F (n : ℤ) : ℝ := if Even n ∧ 32 ≤ |(n:ℝ)| then
    ‖fourierCoeff g n‖^2/(n:ℝ)^4 else 0
  have hn (n : ℤ) : 0 ≤ F n := by dsimp only [F]; split_ifs <;> positivity
  have he (k : ℤ) : F (2*k) = if 16 ≤ k.natAbs then
      ‖fourierCoeff g (2*k)‖^2/(2*(k:ℝ))^4 else 0 := by
    have hiff := even_high_frequency_iff k
    simp only [F,show Even (2*k) from ⟨k,by ring⟩,true_and]
    simp only [hiff]
    simp only [Int.cast_mul,Int.cast_ofNat]
  have hbound (k : ℤ) : F (2*k) ≤ if 16 ≤ k.natAbs then
      1800^2*((k.natAbs-10:ℕ):ℝ)^2*((qb^2:ℚ):ℝ)^(k.natAbs-10) else 0 := by
    rw [he]
    by_cases hk : 16 ≤ k.natAbs
    · rw [if_pos hk,if_pos hk]
      have hk0 : k ≠ 0 := by intro hz; simp only [hz,Int.natAbs_zero] at hk; omega
      have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk0
      have hsq := pow_le_pow_left₀ (norm_nonneg (fourierCoeff g (2*k))) (hb k hk) 2
      apply (div_le_iff₀ (by positivity : 0 < (2*(k:ℝ))^4)).mpr
      convert hsq using 1
      simp only [Rat.cast_pow,← pow_mul]
      rw [Nat.mul_comm 2 (k.natAbs-10)]
      ring
    · simp only [if_neg hk,le_refl]
  have hsum := even_high_geometric_sum (fun k => F (2*k)) ((1800:ℝ)^2)
    10 16 (by decide) (by decide) (qb^2) (by norm_num [qb]) (fun k => hn (2*k)) hbound
  have hodd (n : ℤ) (hn : ¬Even n) : F n = 0 := by simp only [F,hn,false_and,if_false]
  have heq := (even_frequency_sum F hodd hsum.1).2
  rw [← heq] at hsum
  have hnum : (2*(1800:ℝ)^2*(tail2 (qb^2) 6:ℝ)) ≤ (1/8000:ℝ)^2 := by
    have h : (evenLowTestTailSquareUpper:ℝ) ≤ (((1/8000:ℚ)^2:ℚ):ℝ) :=
      Rat.cast_le.mpr even_analytic_coupling_constants.2.1
    simpa only [evenLowTestTailSquareUpper,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
      Rat.cast_div,Rat.cast_one] using h
  exact hsum.2.trans hnum

open scoped ComplexConjugate

theorem circle_bloch_low_sine_high_square_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25) (j : Fin 5)
    (v : Fin 10 → ℂ) (hv : ∑ i, ‖v i‖ ≤ 5) :
    (∑' n : ℤ, if Even n ∧ 32 ≤ |(n:ℝ)| then
      ‖fourierCoeff (circleBlochCoefficient T h h₁ h₂ j (circleSineTrialH4 T 10 v)) n‖^2/
        (n:ℝ)^4 else 0) ≤ (1/8000:ℝ)^2 ∧
    (∑' n : ℤ, if Even n ∧ 32 ≤ |(n:ℝ)| then
      ‖fourierCoeff (circleBlochAdjointCoefficient T h h₁ h₂ j (circleSineTrialH4 T 10 v)) n‖^2/
        (n:ℝ)^4 else 0) ≤ (1/8000:ℝ)^2 := by
  constructor
  · apply circle_even_high_square_of_geometric_bound T
    intro k hk
    exact (circle_bloch_low_sine_high_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr j k hk v hv).1
  · apply circle_even_high_square_of_geometric_bound T
    intro k hk
    exact (circle_bloch_low_sine_high_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr j k hk v hv).2

end Lemniscate
