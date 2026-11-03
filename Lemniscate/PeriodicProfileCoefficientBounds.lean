import Lemniscate.PeriodicProfileBounds
import Lemniscate.WeierstrassFrequencyBounds

/-! Coarse differential-coefficient bounds from the conserved profile
identity. These bounds suffice for the form comparison. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_profile_coefficient_norm_bounds (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x) :
    ‖q^2‖ ≤ 1 ∧ ‖(2:ℂ) • (q*p)‖ ≤ 2 ∧ ‖1-(3:ℂ) • (q^4)‖ ≤ 4 := by
  rcases circle_profile_uniform_norm T q p he hqreal hpreal with ⟨hq,hp⟩
  have hqpow (n : ℕ) : ‖q^n‖ ≤ 1 := by
    exact (norm_pow_le q n).trans (by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg q) hq n)
  refine ⟨hqpow 2,?_,?_⟩
  · rw [norm_smul]
    norm_num only [Complex.norm_ofNat]
    have hm := (norm_mul_le q p).trans (mul_le_mul hq hp (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
    nlinarith only [hm]
  · have ht := norm_sub_le (1:C(AddCircle T, ℂ)) ((3:ℂ) • (q^4))
    rw [norm_smul] at ht
    norm_num only [Complex.norm_ofNat,norm_one] at ht
    linarith only [ht,hqpow 4]

theorem paper_frequency_le_one (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared) :
    2*Real.pi/T ≤ 1 := by
  have hb : Contains ⟨frequencyLower,frequencyUpper⟩ lemniscateFrequencySquared := lemniscate_frequency_bounds
  have hsq : (2*Real.pi/T)^2 ≤ 18/25 := by
    rw [hr]
    exact hb.2.trans (by norm_num [frequencyUpper])
  nlinarith only [hsq,sq_nonneg (2*Real.pi/T-1)]

end Lemniscate
