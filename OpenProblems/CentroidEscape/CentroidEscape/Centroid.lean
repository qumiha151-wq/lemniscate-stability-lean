import CentroidEscape.Geometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp

/-!
# Integral and escape bridge for the reflected expander

The half-orbit and its exact shooting equalities remain explicit inputs.
The additional moment equation m' = x is integrated, not replaced by a
postulated centroid value. The scalar arclength average is defined by its
weighted integral. Numerical existence and positivity must still be proved.
-/

namespace CentroidEscape
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false

lemma integral_reflect_half (f : ℝ → ℝ) (L : ℝ) :
    (∫ s in L..2*L, f (2*L-s)) = ∫ s in 0..L, f s := by
  simpa only [show 2*L-2*L=0 by ring, show 2*L-L=L by ring] using
    intervalIntegral.integral_comp_sub_left (a := L) (b := 2*L) f (2*L)

lemma doubled_coordinate_integrable {z : ℝ → State} {L : ℝ} (hL : 0 ≤ L)
    (hz : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt z (field (z s)) s)
    (hfix : reverseState (z L) = z L) (i : Fin 6) :
    IntervalIntegrable (fun s => doubled z L s i) volume 0 (2*L) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (show 0 ≤ 2*L by linarith)]
  intro s hs
  exact (hasDerivAt_pi.mp (doubled_solves hz hfix hs) i).continuousAt.continuousWithinAt

theorem doubled_x_integral {z : ℝ → State} {L : ℝ} (hL : 0 < L)
    (hz : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt z (field (z s)) s)
    (hfix : reverseState (z L) = z L) :
    (∫ s in 0..2*L, doubled z L s 0) = 2 * ∫ s in 0..L, z s 0 := by
  have hint := doubled_coordinate_integrable hL.le hz hfix 0
  have hleft : (∫ s in 0..L, doubled z L s 0) = ∫ s in 0..L, z s 0 := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hL.le]
    intro s hs
    simp [doubled, hs.2]
  have hright : (∫ s in L..2*L, doubled z L s 0) =
      ∫ s in L..2*L, z (2*L-s) 0 := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro s hs
    simp [doubled, not_le.mpr hs.1, reflected, reverseState]
  have h2 : (0:ℝ) ≤ 2*L := by linarith
  have hL2 : L ≤ 2*L := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (by
      rw [uIcc_of_le hL.le, uIcc_of_le h2]
      exact Icc_subset_Icc le_rfl hL2))
    (hint.mono_set (by
      rw [uIcc_of_le hL2, uIcc_of_le h2]
      exact Icc_subset_Icc hL.le le_rfl))
  rw [hleft, hright, integral_reflect_half (fun s => z s 0) L] at hsplit
  linarith

theorem doubled_y_integral {z : ℝ → State} {L : ℝ} (hL : 0 < L)
    (hz : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt z (field (z s)) s)
    (hfix : reverseState (z L) = z L) :
    (∫ s in 0..2*L, doubled z L s 1) = 0 := by
  have hint := doubled_coordinate_integrable hL.le hz hfix 1
  have hleft : (∫ s in 0..L, doubled z L s 1) = ∫ s in 0..L, z s 1 := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hL.le]
    intro s hs
    simp [doubled, hs.2]
  have hright : (∫ s in L..2*L, doubled z L s 1) =
      ∫ s in L..2*L, -(z (2*L-s) 1) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro s hs
    simp [doubled, not_le.mpr hs.1, reflected, reverseState]
  have h2 : (0:ℝ) ≤ 2*L := by linarith
  have hL2 : L ≤ 2*L := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (by
      rw [uIcc_of_le hL.le, uIcc_of_le h2]
      exact Icc_subset_Icc le_rfl hL2))
    (hint.mono_set (by
      rw [uIcc_of_le hL2, uIcc_of_le h2]
      exact Icc_subset_Icc hL.le le_rfl))
  rw [hleft, hright, intervalIntegral.integral_neg,
    integral_reflect_half (fun s => z s 1) L] at hsplit
  linarith

lemma half_moment_integral {z : ℝ → State} {m : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hz : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt z (field (z s)) s)
    (hm : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt m (z s 0) s) :
    (∫ s in 0..L, z s 0) = m L - m 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · simpa only [uIcc_of_le hL] using hm
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hL]
    intro s hs
    exact (hasDerivAt_pi.mp (hz s hs) 0).continuousAt.continuousWithinAt

/-- Coordinate of the arclength centroid, with the actual speed as weight. -/
def arclengthMean (T : ℝ) (x speed : ℝ → ℝ) : ℝ :=
  (∫ s in 0..T, x s * speed s) / (∫ s in 0..T, speed s)

lemma arclengthMean_constant_speed {T r : ℝ} (hr : r ≠ 0) (x : ℝ → ℝ) :
    arclengthMean T x (fun _ => r) = (∫ s in 0..T, x s) / T := by
  simp only [arclengthMean, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  exact mul_div_mul_right _ _ hr

theorem reflected_centroid_x {z : ℝ → State} {m : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hz : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt z (field (z s)) s)
    (hfix : reverseState (z L) = z L)
    (hm : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt m (z s 0) s) (hm0 : m 0 = 0) :
    arclengthMean (2*L) (fun s => doubled z L s 0) (fun _ => 1) = m L / L := by
  rw [arclengthMean_constant_speed one_ne_zero, doubled_x_integral hL hz hfix,
    half_moment_integral hL.le hz hm, hm0, sub_zero]
  field_simp

theorem reflected_centroid_y {z : ℝ → State} {L : ℝ} (hL : 0 < L)
    (hz : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt z (field (z s)) s)
    (hfix : reverseState (z L) = z L) :
    arclengthMean (2*L) (fun s => doubled z L s 1) (fun _ => 1) = 0 := by
  rw [arclengthMean_constant_speed one_ne_zero, doubled_y_integral hL hz hfix, zero_div]

theorem arclengthMean_scale {T r : ℝ} (hr : r ≠ 0) (x : ℝ → ℝ) :
    arclengthMean T (fun s => r * x s) (fun _ => r) =
      r * arclengthMean T x (fun _ => 1) := by
  rw [arclengthMean_constant_speed hr, arclengthMean_constant_speed one_ne_zero,
    intervalIntegral.integral_const_mul]
  ring

theorem expanderRadius_tendsto : Tendsto expanderRadius atTop atTop := by
  apply (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).comp
  exact tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (by norm_num))

theorem positive_centroid_escapes {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t => expanderRadius t * c) atTop atTop :=
  expanderRadius_tendsto.atTop_mul_const hc

/-- First coordinate of the actual curve's arclength centroid. -/
def curveCentroidX (P : ℝ) (γ : ℝ → Plane) : ℝ :=
  arclengthMean P (fun s => γ s 0) (fun s => ‖deriv γ s‖)

theorem expandingCurve_centroid_x {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1) {t : ℝ} (ht : 0 ≤ t) (P : ℝ) :
    curveCentroidX P (expandingCurve q t) =
      expanderRadius t * ((∫ s in 0..P, q s 0) / P) := by
  have hs : (fun s => ‖deriv (expandingCurve q t) s‖) = fun _ => expanderRadius t := by
    funext s
    exact expandingCurve_speed hq hu ht s
  have hx : (fun s => expandingCurve q t s 0) = fun s => expanderRadius t * q s 0 := by
    funext s
    simp [expandingCurve, position, planePair]
  rw [curveCentroidX, hs, hx, arclengthMean_scale (expanderRadius_pos ht).ne',
    arclengthMean_constant_speed one_ne_zero]

theorem expandingCurve_centroid_escapes {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1)
    (hmean : 0 < (∫ s in 0..P, q s 0) / P) :
    Tendsto (fun t => curveCentroidX P (expandingCurve q t)) atTop atTop := by
  apply (positive_centroid_escapes hmean).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact (expandingCurve_centroid_x hq hu ht P).symm

/-- Conditional analytic end point: exact half-orbit and positive moment give
a global periodic immersed normal flow with divergent arclength centroid.
The existence of these exact shooting and moment data is NOT assumed proved. -/
theorem exact_half_orbit_yields_centroid_escape {z : ℝ → State} {m : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L)
    (hz : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt z (field (z s)) s)
    (h0 : reverseState (z 0) = z 0) (hfix : reverseState (z L) = z L)
    (hu : z 0 2 = 0) (hw : z 0 3 = 1)
    (hm : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt m (z s 0) s)
    (hm0 : m 0 = 0) (hmpos : 0 < m L) :
    ∃ q : ℝ → State,
      Function.Periodic q (2*L) ∧ ContDiff ℝ (⊤ : ℕ∞) q ∧
      (∀ s, HasDerivAt q (field (q s)) s) ∧
      (∀ s, tangentSquare (q s) = 1) ∧
      (∀ t, 0 ≤ t → ∀ s, ‖deriv (expandingCurve q t) s‖ > 0) ∧
      (∀ t, 0 ≤ t → ∀ s,
        inner ℝ (deriv (fun r => expandingCurve q r s) t) (normal (q s)) =
          -scaledForce q (expanderRadius t) (expanderRadius t * s)) ∧
      Tendsto (fun t => curveCentroidX (2*L) (expandingCurve q t)) atTop atTop := by
  have hT : 0 < 2*L := by linarith
  have he : doubled z L 0 = doubled z L (2*L) := by
    rw [doubled_at_zero hL.le, doubled_at_end hL h0]
  have hf : ∀ s ∈ Icc (0:ℝ) (2*L),
      HasDerivAt (doubled z L) (field (doubled z L s)) s :=
    fun s hs => doubled_solves hz hfix hs
  let q := periodize (doubled z L) hT
  have hq : ∀ s, HasDerivAt q (field (q s)) s := periodize_solves hT he hf
  have hunit : ∀ s, tangentSquare (q s) = 1 := by
    intro s
    exact doubled_unit_tangent hL.le hz hfix hu hw
      (Ico_subset_Icc_self (toIcoMod_mem_Ico' hT s))
  have hi : (∫ s in 0..2*L, q s 0) = 2 * m L := by
    have heq : (∫ s in 0..2*L, q s 0) = ∫ s in 0..2*L, doubled z L s 0 := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hT.le]
      intro s hs
      exact congrFun (periodize_eq hT he hs) 0
    rw [heq, doubled_x_integral hL hz hfix, half_moment_integral hL.le hz hm,
      hm0, sub_zero]
  refine ⟨q, periodize_periodic _ hT, periodize_smooth hT he hf, hq, hunit, ?_, ?_, ?_⟩
  · intro t ht s
    rw [expandingCurve_speed hq hunit ht s]
    exact expanderRadius_pos ht
  · intro t ht s
    exact expandingCurve_normal_FEF hq ht s
  · apply expandingCurve_centroid_escapes hq hunit
    rw [hi]
    exact div_pos (mul_pos (by norm_num) hmpos) hT

end
end CentroidEscape
