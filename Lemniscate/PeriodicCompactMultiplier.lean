import Lemniscate.PeriodicBoundedMultiplier
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! An absolutely summable Fourier symbol defines a compact operator.
Its rank-one expansion converges in operator norm, not just pointwise. -/
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFourierRankOne (n : ℤ) : CircleL2 T →L[ℂ] CircleL2 T :=
  InnerProductSpace.rankOne ℂ (fourierBasis (T := T) n) (fourierBasis (T := T) n)

theorem circle_fourier_rank_one_apply (n : ℤ) (f : CircleL2 T) :
    circleFourierRankOne T n f = fourierCoeff f n • fourierBasis (T := T) n := by
  rw [circleFourierRankOne, InnerProductSpace.rankOne_apply,
    ← HilbertBasis.repr_apply_apply, fourierBasis_repr]

theorem circle_fourier_rank_one_norm (n : ℤ) : ‖circleFourierRankOne T n‖ = 1 := by
  simp only [circleFourierRankOne, InnerProductSpace.norm_rankOne,
    (fourierBasis (T := T)).orthonormal.norm_eq_one, mul_one]

theorem circle_fourier_rank_one_compact (n : ℤ) :
    IsCompactOperator (circleFourierRankOne T n) := by
  rw [circleFourierRankOne, InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (innerSL ℂ (fourierBasis (T := T) n))).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℂ (fourierBasis (T := T) n))

theorem circle_multiplier_hasSum_rank_one (m : ℤ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C) (hs : Summable (fun n => ‖m n‖)) :
    HasSum (fun n => m n • circleFourierRankOne T n) (circleBoundedMultiplier T m C hC hm) := by
  have hs' : Summable (fun n => m n • circleFourierRankOne T n) := by
    apply Summable.of_norm
    simpa only [norm_smul, circle_fourier_rank_one_norm, mul_one] using hs
  have heq : (∑' n, m n • circleFourierRankOne T n) =
      circleBoundedMultiplier T m C hC hm := by
    apply ContinuousLinearMap.ext
    intro f
    have h₁ := hs'.hasSum.mapL (ContinuousLinearMap.apply ℂ (CircleL2 T) f)
    have h₂ := (fourierBasis (T := T)).hasSum_repr (circleBoundedMultiplier T m C hC hm f)
    simp only [ContinuousLinearMap.apply_apply, smul_apply,
      circle_fourier_rank_one_apply, smul_smul] at h₁
    simp only [fourierBasis_repr, circle_bounded_multiplier_fourier] at h₂
    exact h₁.unique h₂
  simpa only [heq] using hs'.hasSum

theorem circle_bounded_multiplier_compact (m : ℤ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C) (hs : Summable (fun n => ‖m n‖)) :
    IsCompactOperator (circleBoundedMultiplier T m C hC hm) := by
  apply isCompactOperator_of_tendsto (circle_multiplier_hasSum_rank_one T m C hC hm hs)
  apply Filter.Eventually.of_forall
  intro I
  exact (compactOperator (RingHom.id ℂ) (CircleL2 T) (CircleL2 T)).sum_mem
    (fun n _ => (circle_fourier_rank_one_compact T n).smul (m n))

end Lemniscate
