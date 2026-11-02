import Lemniscate.PeriodicBlochFredholm
import Lemniscate.PeriodicBlochClosed
import Lemniscate.PeriodicProfileCoefficientBounds

/-! Compact resolvent and the eigenvalue characterization for the paper's
actual profile. All coefficient and frequency bounds are discharged here. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem paper_bloch_frequency_bound
    (hr : (2*Real.pi/T)^2 = thetaParameter)
    (α : ℝ) (hα : |α| ≤ 1/2) :
    ‖(α:ℂ)*circleFrequencyFactor T 1‖ ≤ 1 := by
  have htheta : thetaParameter ≤ 1 :=
    actual_nome_theta_r_bounds.2.trans (by norm_num [thetaRUpper])
  have hs := circle_frequency_factor_norm_sq T 1
  simp only [Int.cast_one,one_pow,mul_one,hr] at hs
  have hfreq : ‖circleFrequencyFactor T 1‖ ≤ 1 := by
    nlinarith [norm_nonneg (circleFrequencyFactor T 1)]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ (1/2:ℝ)*1 := mul_le_mul hα hfreq (norm_nonneg _) (by norm_num)
    _ ≤ 1 := by norm_num

theorem paper_bloch_spectrum_iff_eigenvector (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hr : (2*Real.pi/T)^2 = thetaParameter)
    (α : ℝ) (hα : |α| ≤ 1/2) (w : ℂ) :
    w ∈ circleBlochSpectrum T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α ↔
      ∃ u : circleH4Domain T, (u:CircleL2 T) ≠ 0 ∧
        circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α u =
          w • (u:CircleL2 T) := by
  obtain ⟨hh,hh₁,hh₂⟩ := circle_profile_coefficient_norm_bounds T q p he hqreal hpreal
  exact circle_bloch_spectrum_iff_eigenvector T _ _ _ hh hh₁ hh₂ α
    (paper_bloch_frequency_bound T hr α hα) w

theorem paper_bloch_pmap_closed (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hr : (2*Real.pi/T)^2 = thetaParameter)
    (α : ℝ) (hα : |α| ≤ 1/2) :
    (circleBlochPMap T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α).IsClosed := by
  obtain ⟨hh,hh₁,hh₂⟩ := circle_profile_coefficient_norm_bounds T q p he hqreal hpreal
  exact circle_bloch_pmap_closed T _ _ _ hh hh₁ hh₂ α
    (paper_bloch_frequency_bound T hr α hα)

end Lemniscate
