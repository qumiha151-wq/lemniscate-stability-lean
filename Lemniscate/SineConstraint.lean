import Lemniscate.ConcreteCoefficients
import Lemniscate.HigherGeometricMoments

/-! The full infinite coefficient-ratio bound used by the sine constraint.
The Hilbert-space orthogonality step and identification of the rotation
coefficients remain separate obligations. -/
namespace Lemniscate.CoarseArithmetic
open Finset

noncomputable def sineRatio (r q : ℝ) (j : ℕ) : ℝ :=
  (j:ℝ)*evenCoefficient r q j / evenCoefficient r q 1

theorem sineRatio_majorant (r q : ℝ) (k : ℕ)
    (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1) :
    0 ≤ sineRatio r q (k+1) ∧
    sineRatio r q (k+1) ≤ ((k+1:ℕ):ℝ)^2*q^k := by
  have hd1 : 0 < 1-q^2 := sub_pos.mpr (pow_lt_one₀ hq.le hq1 (by decide))
  have hdj : 0 < 1-q^(2*(k+1)) := sub_pos.mpr
    (pow_lt_one₀ hq.le hq1 (by omega))
  have hp : q^(2*(k+1)) ≤ q^2 := pow_le_pow_of_le_one hq.le hq1.le (by omega)
  have hfac : (1-q^2)/(1-q^(2*(k+1))) ≤ 1 :=
    (div_le_one hdj).mpr (by linarith)
  have heq : sineRatio r q (k+1) =
      ((k+1:ℕ):ℝ)^2*q^k*((1-q^2)/(1-q^(2*(k+1)))) := by
    unfold sineRatio evenCoefficient
    simp only [Nat.cast_one, mul_one, pow_succ]
    field_simp [ne_of_gt hr, ne_of_gt hq, ne_of_gt hd1, ne_of_gt hdj]
  rw [heq]
  constructor
  · positivity
  · simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hfac (by positivity : 0 ≤ ((k+1:ℕ):ℝ)^2*q^k)

theorem hasSum_sine_majorant (z : ℝ) (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ => ((n+2:ℕ):ℝ)^4*z^(n+1))
      ((z*(1+11*z+11*z^2+z^3)/(1-z)^5-z)/z) := by
  have hs := (hasSum_nat_add_iff' 2).mpr (hasSum_geometric_moment_four z hz)
  have ht : HasSum (fun n : ℕ => ((n+2:ℕ):ℝ)^4*z^(n+2))
      (z*(1+11*z+11*z^2+z^3)/(1-z)^5-z) := by
    simpa [sum_range_succ] using hs
  convert! ht.div_const z using 1
  ext n
  rw [show n+2 = (n+1)+1 by omega, pow_succ]
  field_simp <;> ring

def sineRhoBound : ℚ := (moment 4 (qhi^2)-qhi^2)/(qhi^2)

theorem hasSum_coarse_sine_majorant :
    HasSum (fun n : ℕ => ((n+2:ℕ):ℝ)^4*((qhi:ℝ)^2)^(n+1))
      (sineRhoBound:ℝ) := by
  simpa [sineRhoBound, moment] using hasSum_sine_majorant ((qhi:ℝ)^2)
    (by norm_num [qhi, Real.norm_eq_abs]) (by norm_num [qhi])

theorem sine_rho_rational_bound : sineRhoBound < (87/500:ℚ)^2 := by decide +kernel

theorem sine_constraint_series_bound (r q : ℝ)
    (hr : 0 < r) (hq : Contains ⟨qlo,qhi⟩ q) :
    Summable (fun n : ℕ => (sineRatio r q (n+2))^2) ∧
    (∑' n : ℕ, (sineRatio r q (n+2))^2) < (87/500:ℝ)^2 := by
  have hq0 : 0 < q := (by norm_num [qlo] : (0:ℝ) < (qlo:ℝ)).trans_le hq.1
  have hq1 : q < 1 := hq.2.trans_lt (by norm_num [qhi])
  have hmajor : ∀ n : ℕ, (sineRatio r q (n+2))^2 ≤
      ((n+2:ℕ):ℝ)^4*((qhi:ℝ)^2)^(n+1) := by
    intro n
    have h := sineRatio_majorant r q (n+1) hr hq0 hq1
    have hpow := pow_le_pow_left₀ hq0.le hq.2 (n+1)
    have hu : sineRatio r q (n+2) ≤ ((n+2:ℕ):ℝ)^2*(qhi:ℝ)^(n+1) :=
      h.2.trans (mul_le_mul_of_nonneg_left hpow (sq_nonneg _))
    calc
      _ ≤ (((n+2:ℕ):ℝ)^2*(qhi:ℝ)^(n+1))^2 := pow_le_pow_left₀ h.1 hu 2
      _ = _ := by
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm (n+1) 2]
  have hs := Summable.of_nonneg_of_le (fun n => sq_nonneg (sineRatio r q (n+2)))
    hmajor hasSum_coarse_sine_majorant.summable
  refine ⟨hs, ?_⟩
  have hu := hs.tsum_le_tsum hmajor hasSum_coarse_sine_majorant.summable
  rw [hasSum_coarse_sine_majorant.tsum_eq] at hu
  apply hu.trans_lt
  have hc := (Rat.cast_lt (K := ℝ)).mpr sine_rho_rational_bound
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using hc

theorem theta_nome_sine_constraint_bound :
    (∑' n : ℕ, (sineRatio thetaParameter nome (n+2))^2) < (87/500:ℝ)^2 :=
  (sine_constraint_series_bound _ _
    ((by norm_num [rlo] : (0:ℝ) < (rlo:ℝ)).trans_le (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1)
    (refined_nome_bounds.mono (by norm_num [qlo, nomeLower]) (by norm_num [qhi, nomeUpper]))).2

end Lemniscate.CoarseArithmetic
