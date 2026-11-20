import Migration.SeparatedEndpointEnergy
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity

noncomputable section
open Finset
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion

/-- For a once-covered expanding circle, time and energy in the radius
variable are `r^4/2 + constant` and `π/r`. -/
theorem round_time_energy_cost {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    Real.pi/2*(b-a)^3 ≤ ((b^4-a^4)/2)*(Real.pi/a-Real.pi/b) := by
  have hb := ha.trans_le hab
  have hident : ((b^4-a^4)/2)*(Real.pi/a-Real.pi/b)-Real.pi/2*(b-a)^3 =
      (Real.pi/2)*(b-a)^2*(b^3+2*a^2*b+a^3)/(a*b) := by
    field_simp
    ring
  have hge : 0 ≤ (Real.pi/2)*(b-a)^2*(b^3+2*a^2*b+a^3)/(a*b) := by positivity
  linarith

theorem round_budget_dominates_increment {a b d : ℝ} (ha : 0<a) (hab : a≤b) (hd : 0≤d)
    (hcharge : ((b^4-a^4)/2)*(Real.pi/a-Real.pi/b) ≤ widthTransitCost d (Real.pi/a)) :
    2*(b-a) ≤ d := by
  have hπ := Real.pi_pos
  have hden : Real.pi^2 ≤ (Real.pi+Real.sqrt (2*(Real.pi/a)*d))^2 := by
    have h := Real.sqrt_nonneg (2*(Real.pi/a)*d)
    nlinarith [mul_nonneg hπ.le h, sq_nonneg (Real.sqrt (2*(Real.pi/a)*d))]
  have hcost : widthTransitCost d (Real.pi/a) ≤ d^3/Real.pi^2 :=
    div_le_div_of_nonneg_left (pow_nonneg hd 3) (sq_pos_of_pos hπ) hden
  have h₁ := (le_div_iff₀ (sq_pos_of_pos hπ)).mp ((round_time_energy_cost ha hab).trans
    (hcharge.trans hcost))
  have hπ3 : 16 ≤ Real.pi^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) Real.pi_gt_three.le 3
    norm_num at h
    linarith
  have h₂ := mul_le_mul_of_nonneg_right hπ3 (pow_nonneg (sub_nonneg.mpr hab) 3)
  by_contra! hbad
  have h₃ := pow_lt_pow_left₀ hbad hd (by norm_num : (3:ℕ) ≠ 0)
  nlinarith

/-- The worst-case directional losses required by this cutoff estimate
cannot be summed to a bounded budget along an expanding round circle. -/
theorem round_partition_budget (R d : ℕ → ℝ) (n : ℕ) (hp : ∀ j, 0<R j)
    (hm : ∀ j < n, R j ≤ R (j+1)) (hd : ∀ j < n, 0 ≤ d j)
    (hc : ∀ j < n, ((R (j+1)^4-R j^4)/2)*(Real.pi/(R j)-Real.pi/(R (j+1))) ≤
      widthTransitCost (d j) (Real.pi/(R j))) :
    2*(R n-R 0) ≤ ∑ j ∈ range n, d j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun j hj => hm j (Nat.lt_succ_of_lt hj))
      (fun j hj => hd j (Nat.lt_succ_of_lt hj)) (fun j hj => hc j (Nat.lt_succ_of_lt hj))
    have hlast := round_budget_dominates_increment (hp n) (hm n (Nat.lt_succ_self _))
      (hd n (Nat.lt_succ_self _)) (hc n (Nat.lt_succ_self _))
    rw [sum_range_succ]
    linarith

#print axioms round_partition_budget
end MigrationGeometry.Flow.SmoothPeriodicImmersion
