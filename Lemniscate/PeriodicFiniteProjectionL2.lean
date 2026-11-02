import Lemniscate.PeriodicFiniteBlochForm
import Lemniscate.EvenCouplingEntryBounds

/-! Ordinary L2 orthogonality of the fixed projection, and the coarse
comparison with the already certified low-frequency energy weights. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

private theorem rank_one_projection_norm_split {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (a f : E) (ha : inner ℂ a a = 1) :
    ‖f-inner ℂ a f • a‖^2+‖inner ℂ a f • a‖^2 = ‖f‖^2 := by
  have hfa : inner ℂ f a = conj (inner ℂ a f) := (inner_conj_symm f a).symm
  have hi : inner ℂ (f-inner ℂ a f • a) (f-inner ℂ a f • a)+
      inner ℂ (inner ℂ a f • a) (inner ℂ a f • a) = inner ℂ f f := by
    simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,ha,hfa]
    ring
  have h := congrArg Complex.re hi
  simpa [inner_self_eq_norm_sq_to_K,pow_two] using h

variable (T : ℝ) [Fact (0 < T)]

theorem circle_fixed_projection_l2_norm_split (f : circleH4Domain T) :
    ‖f-circleFixedProjectionH4 T f‖^2+‖circleFixedProjectionH4 T f‖^2 = ‖f‖^2 := by
  have h := rank_one_projection_norm_split (circleHouseholderAnchor T) (f:CircleL2 T)
    (circle_householder_anchor_unit T)
  change ‖((f-circleFixedProjectionH4 T f:circleH4Domain T):CircleL2 T)‖^2+
    ‖(circleFixedProjectionH4 T f:CircleL2 T)‖^2 = ‖(f:CircleL2 T)‖^2
  simpa only [circleFixedProjectionH4,Submodule.coe_sub,Submodule.coe_smul_of_tower,
    circle_householder_anchor_h4_coe] using h

theorem circle_even_head_norm_le_weighted_energy (v : Fin 31 → ℂ) :
    ‖circleEvenHeadH4 T v‖^2 ≤ 16*(∑ i : Fin 31, (evenFactorPenalty i:ℝ)*‖v i‖^2) := by
  change ‖(circleEvenHeadH4 T v:CircleL2 T)‖^2 ≤ _
  rw [circle_even_head_norm_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hd : (1/16:ℝ) ≤ (evenFactorPenalty i:ℝ) := by
    rw [even_factor_penalty_values i]
    have h : ((1/16:ℚ):ℝ) ≤ (evenModePenalty (evenHeadFrequency i):ℝ) :=
      Rat.cast_le.mpr (even_mode_penalty_lower _)
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  nlinarith only [mul_le_mul_of_nonneg_right hd (sq_nonneg ‖v i‖)]

end Lemniscate
