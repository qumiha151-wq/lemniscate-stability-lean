import Mathlib.Analysis.Complex.Liouville
import Mathlib.Algebra.Ring.Periodic

noncomputable section
open Complex Set Function Bornology Metric
namespace ClosedSimilarity.MeromorphicCurvature

/-- Subtracting period multiples places the argument in a bounded rectangle. -/
theorem periodic_plane_range {f : ℂ → ℂ} {P : ℝ} {v : ℂ}
    (hp : 0 < P) (hv : 0 < v.im) (hP : Periodic f (P : ℂ)) (hV : Periodic f v) :
    range f ⊆ f '' closedBall (0 : ℂ) (P + v.im) := by
  rintro _ ⟨z,rfl⟩
  let n : ℤ := ⌊z.im / v.im⌋
  let w : ℂ := z - n • v
  let m : ℤ := ⌊w.re / P⌋
  let t : ℂ := w - m • (P : ℂ)
  have hni : (n:ℝ)*v.im ≤ z.im := (le_div_iff₀ hv).mp (Int.floor_le _)
  have hns : z.im < ((n:ℝ)+1)*v.im := (div_lt_iff₀ hv).mp (Int.lt_floor_add_one _)
  have hmi : (m:ℝ)*P ≤ w.re := (le_div_iff₀ hp).mp (Int.floor_le _)
  have hms : w.re < ((m:ℝ)+1)*P := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one _)
  have wi : w.im = z.im-(n:ℝ)*v.im := by simp [w,zsmul_eq_mul]
  have tr : t.re = w.re-(m:ℝ)*P := by simp [t,zsmul_eq_mul]
  have ti : t.im = w.im := by simp [t,zsmul_eq_mul]
  refine ⟨t, ?_, (hP.sub_zsmul_eq m).trans (hV.sub_zsmul_eq n)⟩
  rw [mem_closedBall, dist_zero_right]
  apply (Complex.norm_le_abs_re_add_abs_im t).trans
  rw [abs_of_nonneg (by linarith : 0 ≤ t.re), abs_of_nonneg (by linarith : 0 ≤ t.im)]
  linarith

/-- Liouville's theorem for a horizontal and a transverse period. -/
theorem entire_two_periods_constant {f : ℂ → ℂ} {P : ℝ} {v : ℂ}
    (hf : Differentiable ℂ f) (hp : 0<P) (hv : 0<v.im)
    (hP : Periodic f (P:ℂ)) (hV : Periodic f v) (x y : ℂ) : f x = f y := by
  apply hf.apply_eq_apply_of_bounded _ x y
  exact ((isCompact_closedBall (0:ℂ) (P+v.im)).image hf.continuous).isBounded.subset
    (periodic_plane_range hp hv hP hV)

end ClosedSimilarity.MeromorphicCurvature

