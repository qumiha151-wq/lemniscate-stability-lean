import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Necessary backtracking for a curvature profile joining the two oriented
unit-circle states. Only the Frenet support equations are assumed; the
elastic profile equation and any alignment at curvature zeros are absent.
This does not prove existence of a connecting profile or a length-growth bound.
-/

noncomputable section
open Filter
open scoped Topology

namespace LengthGrowth.CircleConnection

structure SupportProfile where
  U : ℝ → ℝ
  v : ℝ → ℝ
  p : ℝ → ℝ
  q : ℝ → ℝ
  U_deriv : ∀ s, HasDerivAt U (v s) s
  p_deriv : ∀ s, HasDerivAt p (-U s * q s) s
  q_deriv : ∀ s, HasDerivAt q (1 + U s * p s) s

namespace SupportProfile

variable (c : SupportProfile)

def radiusSq (s : ℝ) : ℝ := c.p s ^ 2 + c.q s ^ 2
def balance (s : ℝ) : ℝ := c.U s * c.radiusSq s + 2 * c.p s

theorem radiusSq_nonneg (s : ℝ) : 0 ≤ c.radiusSq s :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem radiusSq_deriv (s : ℝ) : HasDerivAt c.radiusSq (2 * c.q s) s := by
  convert! ((c.p_deriv s).pow 2).add ((c.q_deriv s).pow 2) using 1 <;> ring

theorem balance_deriv (s : ℝ) :
    HasDerivAt c.balance (c.v s * c.radiusSq s) s := by
  convert! ((c.U_deriv s).mul (c.radiusSq_deriv s)).add
    ((c.p_deriv s).const_mul 2) using 1 <;> ring

theorem balance_monotone_of_nonneg (hv : ∀ s, 0 ≤ c.v s) :
    Monotone c.balance :=
  monotone_of_hasDerivAt_nonneg c.balance_deriv
    (fun s => mul_nonneg (hv s) (c.radiusSq_nonneg s))

theorem balance_limit {l : Filter ℝ} {u p q : ℝ}
    (hU : Tendsto c.U l (𝓝 u)) (hp : Tendsto c.p l (𝓝 p))
    (hq : Tendsto c.q l (𝓝 q)) :
    Tendsto c.balance l (𝓝 (u * (p ^ 2 + q ^ 2) + 2 * p)) := by
  exact (hU.mul ((hp.pow 2).add (hq.pow 2))).add (hp.const_mul 2)

/-- The geometry alone forces a point of strictly decreasing curvature.
No decay rate or integrability assumption on the infinite tails is used. -/
theorem exists_negative_derivative
    (hU_left : Tendsto c.U atBot (𝓝 (-1)))
    (hp_left : Tendsto c.p atBot (𝓝 1))
    (hq_left : Tendsto c.q atBot (𝓝 0))
    (hU_right : Tendsto c.U atTop (𝓝 1))
    (hp_right : Tendsto c.p atTop (𝓝 (-1)))
    (hq_right : Tendsto c.q atTop (𝓝 0)) :
    ∃ s, c.v s < 0 := by
  by_contra h
  have hv : ∀ s, 0 ≤ c.v s := by simpa only [not_exists, not_lt] using h
  have hm := c.balance_monotone_of_nonneg hv
  have hleft : Tendsto c.balance atBot (𝓝 1) := by
    convert c.balance_limit hU_left hp_left hq_left using 1
    norm_num
  have hright : Tendsto c.balance atTop (𝓝 (-1)) := by
    convert c.balance_limit hU_right hp_right hq_right using 1
    norm_num
  have hl : 1 ≤ c.balance 0 := le_of_tendsto hleft
    ((eventually_le_atBot (0 : ℝ)).mono fun _ hs => hm hs)
  have hr : c.balance 0 ≤ -1 := ge_of_tendsto hright
    ((eventually_ge_atTop (0 : ℝ)).mono fun _ hs => hm hs)
  linarith

theorem not_monotone_curvature
    (hU_left : Tendsto c.U atBot (𝓝 (-1)))
    (hp_left : Tendsto c.p atBot (𝓝 1))
    (hq_left : Tendsto c.q atBot (𝓝 0))
    (hU_right : Tendsto c.U atTop (𝓝 1))
    (hp_right : Tendsto c.p atTop (𝓝 (-1)))
    (hq_right : Tendsto c.q atTop (𝓝 0)) :
    ¬ Monotone c.U := by
  intro hU
  obtain ⟨s, hs⟩ := c.exists_negative_derivative
    hU_left hp_left hq_left hU_right hp_right hq_right
  have hn := hU.deriv_nonneg (x := s)
  rw [(c.U_deriv s).deriv] at hn
  exact (not_lt_of_ge hn) hs

end SupportProfile
end LengthGrowth.CircleConnection

#print axioms LengthGrowth.CircleConnection.SupportProfile.exists_negative_derivative
#print axioms LengthGrowth.CircleConnection.SupportProfile.not_monotone_curvature
