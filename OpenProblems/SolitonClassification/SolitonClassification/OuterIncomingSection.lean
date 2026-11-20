import SolitonClassification.OuterIncomingCoordinates

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set

/-- The exact scale cancellation turns the outer estimate into an inverse
    height bound on the true physical impact at *every* crossing. -/
theorem impact_at_level {x : Phase} {δ C m H : ℝ}
    (reg : regular x) (far : 1 ≤ innerRoot x) (hm : 0<m)
    (rad : m≤outerRadius δ x) (large : 2≤H) (hit : -height x=H)
    (outer : |impact x| * (innerRoot x)^2*(outerRadius δ x)^2 ≤ C) :
    |impact x| ≤ 2*C/(m^2*H) := by
  have err := abs_le.mp (height_error reg far)
  rw [hit] at err
  have unit := (unit_chart x reg).2
  have al : along x ≤ 1 := by nlinarith [sq_nonneg (across x),sq_nonneg (along x-1)]
  have hcap : H≤(innerRoot x)^2+1 := by
    linarith [mul_le_mul_of_nonneg_left al (sq_nonneg (innerRoot x)),err.2]
  have use : H≤2*(innerRoot x)^2 := by linarith
  have e := mul_le_mul use (pow_le_pow_left₀ hm.le rad 2) (sq_nonneg m) (by positivity)
  have fin := mul_le_mul_of_nonneg_left e (abs_nonneg (impact x))
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [fin,outer]

theorem crossing_on_strip {x : ℝ→Phase} {S T H : ℝ} (st : S≤T) (cont : ContinuousOn x (Icc S T))
    (data : ∀s∈Icc S T, regular (x s) ∧ 1 ≤ innerRoot (x s))
    (start : H+1 ≤ (innerRoot (x S))^2*along (x S))
    (finish : (innerRoot (x T))^2+1 ≤ H) :
    ∃t∈Icc S T, -height (x t)=H := by
  have ds := data S (left_mem_Icc.mpr st)
  have dt := data T (right_mem_Icc.mpr st)
  have lo := (abs_le.mp (height_error ds.1 ds.2)).1
  have hi := (abs_le.mp (height_error dt.1 dt.2)).2
  have un := (unit_chart _ dt.1).2
  have a : along (x T) ≤ 1 := by nlinarith [sq_nonneg (across (x T)),sq_nonneg (along (x T)-1)]
  apply intermediate_value_Icc' st (fun t ht =>
    (((height_smooth (data t ht).1).continuousAt.comp_continuousWithinAt (cont t ht)).neg))
  change H ∈ Icc (-height (x T)) (-height (x S))
  exact ⟨by linarith [mul_le_mul_of_nonneg_left a (sq_nonneg (innerRoot (x T)))],by linarith⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.impact_at_level
