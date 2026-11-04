import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

/-! Completion of actual approximate solutions. The source is complete;
the target need not be complete, and the data map need not be linear.
A difference estimate for the approximants and a continuous energy bound
pass to the limit along a sequence of dense data.
-/
noncomputable section
namespace Lemniscate
open Filter
open scoped Topology

/-- Dense approximate solvability with a uniform difference estimate gives
an actual solution satisfying the same continuous square-norm bound. -/
theorem banach_dense_solvability
    {E X D : Type*} [NormedAddCommGroup E] [CompleteSpace E] [NormedAddCommGroup X]
    (J : E → X) (hJ : Continuous J) (v : D → E)
    (hdense : ∀ x : X, ∀ ε : ℝ, 0 < ε → ∃ d : D, ‖J (v d)-x‖ < ε)
    (A : ℝ) (hA : 0 ≤ A)
    (hdiff : ∀ d e : D, ‖v d-v e‖ ≤ A*‖J (v d)-J (v e)‖)
    (b : X → ℝ) (hb : Continuous b) (hbound : ∀ d : D, ‖v d‖^2 ≤ b (J (v d)))
    (x : X) : ∃ U : E, J U = x ∧ ‖U‖^2 ≤ b x := by
  have happrox (n : ℕ) : ∃ d : D, ‖J (v d)-x‖ < 1/((n:ℝ)+1) :=
    hdense x _ (by positivity)
  choose d hd using happrox
  have hdata : Tendsto (fun n => J (v (d n))) atTop (𝓝 x) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hCauchy : CauchySeq (fun n => v (d n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hden : 0 < A+1 := add_pos_of_nonneg_of_pos hA zero_lt_one
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hdata.cauchySeq
      (ε/(A+1)) (div_pos hε hden)
    refine ⟨N,fun n hn m hm => ?_⟩
    have hsmall : ‖J (v (d n))-J (v (d m))‖ < ε/(A+1) := by
      simpa only [dist_eq_norm] using hN n hn m hm
    have hstrict : A*(ε/(A+1)) < ε := by
      have hp : 0 < ε/(A+1) := div_pos hε hden
      have hc : (A+1)*(ε/(A+1)) = ε := mul_div_cancel₀ ε hden.ne'
      linear_combination hp+hc
    calc
      dist (v (d n)) (v (d m)) = ‖v (d n)-v (d m)‖ := dist_eq_norm _ _
      _ ≤ A*‖J (v (d n))-J (v (d m))‖ := hdiff (d n) (d m)
      _ ≤ A*(ε/(A+1)) := mul_le_mul_of_nonneg_left hsmall.le hA
      _ < ε := hstrict
  obtain ⟨U,hU⟩ := cauchySeq_tendsto_of_complete hCauchy
  refine ⟨U,tendsto_nhds_unique ((hJ.tendsto U).comp hU) hdata,?_⟩
  exact le_of_tendsto_of_tendsto (hU.norm.pow 2) ((hb.tendsto x).comp hdata)
    (Eventually.of_forall fun n => hbound (d n))

end Lemniscate
