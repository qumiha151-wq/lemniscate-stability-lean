import Lemniscate.NomeBounds
import Lemniscate.GeometricTails
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Convergence of the theta series and the coarse enclosure of its negative
fourth power. Identification with (pi/(2K))^2 remains a separate obligation. -/
namespace Lemniscate.CoarseArithmetic
open Finset

theorem summable_theta (q : ℝ) (hq : Contains ⟨qlo,qhi⟩ q) :
    Summable (fun n : ℕ => q^((n+1)^2)) := by
  have hq0 : 0 ≤ q := (by norm_num [qlo] : (0:ℝ) ≤ (qlo:ℝ)).trans hq.1
  have hs := (hasSum_geometric_of_norm_lt_one
    (by norm_num [qhi, Real.norm_eq_abs] : ‖(qhi:ℝ)‖ < 1)).summable
  apply Summable.of_nonneg_of_le (fun n => pow_nonneg hq0 _) _ hs
  intro n
  apply (pow_le_pow_left₀ hq0 hq.2 _).trans
  apply pow_le_pow_of_le_one (by norm_num [qhi]) (by norm_num [qhi])
  nlinarith

noncomputable def thetaValue (q : ℝ) : ℝ := 1+2*(∑' n : ℕ, q^((n+1)^2))
noncomputable def thetaR (q : ℝ) : ℝ := 1/(thetaValue q)^4

def thetaLower : ℚ := 1+2*qlo+2*qlo^4
def thetaUpper : ℚ := 1+2*qhi+2*qhi^4/(1-qhi^5)

theorem theta_tail_majorant (q : ℝ) (hq : Contains ⟨qlo,qhi⟩ q) (n : ℕ) :
    q^((n+2)^2) ≤ (qhi:ℝ)^4*((qhi:ℝ)^5)^n := by
  have hq0 : 0 ≤ q := (by norm_num [qlo] : (0:ℝ) ≤ (qlo:ℝ)).trans hq.1
  apply (pow_le_pow_left₀ hq0 hq.2 _).trans
  rw [← pow_mul, ← pow_add]
  apply pow_le_pow_of_le_one (by norm_num [qhi]) (by norm_num [qhi])
  rcases n with _ | n <;> nlinarith

theorem theta_enclosure (q : ℝ) (hq : Contains ⟨qlo,qhi⟩ q) :
    Contains ⟨thetaLower,thetaUpper⟩ (thetaValue q) := by
  have hq0 : 0 ≤ q := (by norm_num [qlo] : (0:ℝ) ≤ (qlo:ℝ)).trans hq.1
  have hs := summable_theta q hq
  have hlo := hs.sum_le_tsum (range 2) (fun n _ => pow_nonneg hq0 _)
  norm_num [sum_range_succ] at hlo
  have hp4 := pow_le_pow_left₀ (by norm_num [qlo] : (0:ℝ) ≤ (qlo:ℝ)) hq.1 4
  have hgeom := (hasSum_geometric_of_norm_lt_one
    (by norm_num [qhi, Real.norm_eq_abs] : ‖(qhi:ℝ)^5‖ < 1)).mul_left ((qhi:ℝ)^4)
  have htailS : Summable (fun n : ℕ => q^((n+2)^2)) :=
    Summable.of_nonneg_of_le (fun n => pow_nonneg hq0 _)
      (theta_tail_majorant q hq) hgeom.summable
  have htail := htailS.tsum_le_tsum (theta_tail_majorant q hq) hgeom.summable
  rw [hgeom.tsum_eq] at htail
  have hsplit := hs.sum_add_tsum_nat_add 1
  norm_num [sum_range_succ, Nat.add_assoc] at hsplit
  constructor
  · change (thetaLower:ℝ) ≤ thetaValue q
    simp only [thetaLower, thetaValue, Rat.cast_add, Rat.cast_mul, Rat.cast_one,
      Rat.cast_ofNat, Rat.cast_pow]
    linarith only [hlo, hp4, hq.1]
  · change thetaValue q ≤ (thetaUpper:ℝ)
    simp only [thetaUpper, thetaValue, Rat.cast_add, Rat.cast_mul, Rat.cast_one,
      Rat.cast_ofNat, Rat.cast_pow, Rat.cast_div, Rat.cast_sub]
    have htail' : 2*(∑' n : ℕ, q^((n+2)^2)) ≤
        2*(qhi:ℝ)^4/(1-(qhi:ℝ)^5) := by
      calc
        _ ≤ 2*((qhi:ℝ)^4*(1-(qhi:ℝ)^5)⁻¹) :=
          mul_le_mul_of_nonneg_left htail (by norm_num)
        _ = _ := by ring
    linarith only [htail', hsplit, hq.2]

theorem coarse_theta_r_bounds (q : ℝ) (hq : Contains ⟨qlo,qhi⟩ q) :
    Contains ⟨rlo,rhi⟩ (thetaR q) := by
  have ht := theta_enclosure q hq
  have ht0 : 0 < thetaValue q :=
    (by norm_num [thetaLower, qlo] : (0:ℝ) < (thetaLower:ℝ)).trans_le ht.1
  have hlo : (thetaLower:ℝ)^4 ≤ (thetaValue q)^4 :=
    pow_le_pow_left₀ (by norm_num [thetaLower, qlo]) ht.1 4
  have hhi : (thetaValue q)^4 ≤ (thetaUpper:ℝ)^4 := pow_le_pow_left₀ ht0.le ht.2 4
  constructor
  · change (rlo:ℝ) ≤ 1/(thetaValue q)^4
    apply le_trans _ (one_div_le_one_div_of_le (pow_pos ht0 4) hhi)
    norm_num [rlo, thetaUpper, qhi]
  · change 1/(thetaValue q)^4 ≤ (rhi:ℝ)
    apply le_trans (one_div_le_one_div_of_le
      (by norm_num [thetaLower, qlo] : (0:ℝ) < (thetaLower:ℝ)^4) hlo)
    norm_num [rhi, thetaLower, qlo]

theorem actual_nome_theta_r_bounds :
    Contains ⟨rlo,rhi⟩ (thetaR (Real.exp (-Real.pi))) :=
  coarse_theta_r_bounds _ coarse_nome_bounds

end Lemniscate.CoarseArithmetic
