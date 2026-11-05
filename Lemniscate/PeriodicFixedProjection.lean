import Lemniscate.PeriodicHouseholderAnchor

/-! The exact rank-one projection, independent of finite approximations. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFixedProjectionH4 (f : circleH4Domain T) : circleH4Domain T :=
  inner ℂ (circleHouseholderAnchor T) (f : CircleL2 T) • circleHouseholderAnchorH4 T

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

theorem circle_fixed_projection_l2_norm_split (f : circleH4Domain T) :
    ‖f-circleFixedProjectionH4 T f‖^2+‖circleFixedProjectionH4 T f‖^2 = ‖f‖^2 := by
  have h := rank_one_projection_norm_split (circleHouseholderAnchor T) (f:CircleL2 T)
    (circle_householder_anchor_unit T)
  change ‖((f-circleFixedProjectionH4 T f:circleH4Domain T):CircleL2 T)‖^2+
    ‖(circleFixedProjectionH4 T f:CircleL2 T)‖^2 = ‖(f:CircleL2 T)‖^2
  simpa only [circleFixedProjectionH4,Submodule.coe_sub,Submodule.coe_smul_of_tower,
    circle_householder_anchor_h4_coe] using h

end Lemniscate
