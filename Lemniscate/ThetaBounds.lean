import Lemniscate.NomeBounds
import Lemniscate.GeometricTails
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Convergence of the theta series and a three-term enclosure of its negative
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

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def thetaLower : ℚ := 1086434811213308014574 / 10^21
def thetaUpper : ℚ := 1086434811213308014577 / 10^21

theorem theta_enclosure :
    Contains ⟨thetaLower,thetaUpper⟩ (thetaValue (Real.exp (-Real.pi))) := by
  let q := Real.exp (-Real.pi)
  have hq : Contains ⟨nomeLower,nomeUpper⟩ q := refined_nome_bounds
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hlow0 : (0:ℝ) ≤ (nomeLower:ℝ) := by norm_num [nomeLower]
  have hupp0 : (0:ℝ) ≤ (nomeUpper:ℝ) := by norm_num [nomeUpper]
  have hupp1 : (nomeUpper:ℝ) ≤ 1 := by norm_num [nomeUpper]
  have hs := summable_theta q
    (hq.mono (by norm_num [qlo,nomeLower]) (by norm_num [qhi,nomeUpper]))
  have hheadLow : (∑ n ∈ range 3, (nomeLower:ℝ)^((n+1)^2)) ≤
      ∑ n ∈ range 3, q^((n+1)^2) := by
    apply sum_le_sum
    intro n hn
    exact pow_le_pow_left₀ hlow0 hq.1 _
  have hheadHigh : (∑ n ∈ range 3, q^((n+1)^2)) ≤
      ∑ n ∈ range 3, (nomeUpper:ℝ)^((n+1)^2) := by
    apply sum_le_sum
    intro n hn
    exact pow_le_pow_left₀ hq0 hq.2 _
  have hlo := hs.sum_le_tsum (range 3) (fun n _ => pow_nonneg hq0 _)
  have hmajor (n : ℕ) : q^((n+4)^2) ≤
      (nomeUpper:ℝ)^16*((nomeUpper:ℝ)^9)^n := by
    apply (pow_le_pow_left₀ hq0 hq.2 _).trans
    rw [← pow_mul, ← pow_add]
    apply pow_le_pow_of_le_one hupp0 hupp1
    rcases n with _ | n <;> nlinarith
  have hgeom := (hasSum_geometric_of_norm_lt_one
    (by norm_num [nomeUpper,Real.norm_eq_abs] : ‖(nomeUpper:ℝ)^9‖ < 1)).mul_left
      ((nomeUpper:ℝ)^16)
  have htailS : Summable (fun n : ℕ => q^((n+4)^2)) :=
    Summable.of_nonneg_of_le (fun n => pow_nonneg hq0 _) hmajor hgeom.summable
  have htail := htailS.tsum_le_tsum hmajor hgeom.summable
  rw [hgeom.tsum_eq] at htail
  have hsplit := hs.sum_add_tsum_nat_add 3
  simp only [Nat.add_assoc] at hsplit
  constructor
  · change (thetaLower:ℝ) ≤ 1+2*(∑' n : ℕ, q^((n+1)^2))
    have hl : (thetaLower:ℝ) ≤
        1+2*∑ n ∈ range 3, (nomeLower:ℝ)^((n+1)^2) := by
      norm_num [thetaLower,nomeLower,sum_range_succ]
    linarith only [hl,hheadLow,hlo]
  · change 1+2*(∑' n : ℕ, q^((n+1)^2)) ≤ (thetaUpper:ℝ)
    have ht : 2*(∑' n : ℕ, q^((n+4)^2)) ≤ 2*(nomeUpper:ℝ)^16/(1-(nomeUpper:ℝ)^9) := by
      calc
        _ ≤ 2*((nomeUpper:ℝ)^16*(1-(nomeUpper:ℝ)^9)⁻¹) :=
          mul_le_mul_of_nonneg_left htail (by norm_num)
        _ = _ := by ring
    have hu : 1+2*(∑ n ∈ range 3, (nomeUpper:ℝ)^((n+1)^2))+
        2*(nomeUpper:ℝ)^16/(1-(nomeUpper:ℝ)^9) ≤ (thetaUpper:ℝ) := by
      norm_num [thetaUpper,nomeUpper,sum_range_succ]
    linarith only [hu,ht,hheadHigh,hsplit]

def thetaRLower : ℚ := 717770011046129997816 / 10^21
def thetaRUpper : ℚ := 717770011046129997825 / 10^21

theorem actual_nome_theta_r_bounds :
    Contains ⟨thetaRLower,thetaRUpper⟩ (thetaR (Real.exp (-Real.pi))) := by
  have ht := theta_enclosure
  have hlo0 : (0:ℝ) < (thetaLower:ℝ) := by norm_num [thetaLower]
  have ht0 := hlo0.trans_le ht.1
  have hlo : (thetaLower:ℝ)^4 ≤ (thetaValue (Real.exp (-Real.pi)))^4 :=
    pow_le_pow_left₀ hlo0.le ht.1 4
  have hhi : (thetaValue (Real.exp (-Real.pi)))^4 ≤ (thetaUpper:ℝ)^4 :=
    pow_le_pow_left₀ ht0.le ht.2 4
  constructor
  · change (thetaRLower:ℝ) ≤ 1/(thetaValue (Real.exp (-Real.pi)))^4
    apply le_trans _ (one_div_le_one_div_of_le (pow_pos ht0 4) hhi)
    norm_num [thetaRLower,thetaUpper]
  · change 1/(thetaValue (Real.exp (-Real.pi)))^4 ≤ (thetaRUpper:ℝ)
    apply le_trans (one_div_le_one_div_of_le (pow_pos hlo0 4) hlo) _
    norm_num [thetaRUpper,thetaLower]

end Lemniscate.CoarseArithmetic
