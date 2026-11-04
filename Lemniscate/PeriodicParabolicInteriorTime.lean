import Lemniscate.PeriodicParabolicGlobalSolution
import Mathlib.Algebra.Order.Floor.Semiring

/-! Uniform interior coordinates for overlapping parabolic segments.

-/
noncomputable section
namespace Lemniscate
open scoped NNReal

/-- Every time bounded away from zero has a segment coordinate uniformly
bounded away from the left endpoint and strictly below the right endpoint. -/
theorem circle_parabolic_interior_time
    (τ : ℝ) (hτ : 0 < τ) (t₀ : ℝ) (ht₀ : 0 < t₀)
    (t : ℝ≥0) (ht : t₀ ≤ (t:ℝ)) :
    ∃ (n : ℕ) (r : unitInterval),
      (r:ℝ) < 1 ∧ min (1/2:ℝ) (t₀/τ) ≤ (r:ℝ) ∧
        circleParabolicSegmentTime τ hτ n r = t := by
  let q : ℝ := (t:ℝ)/τ
  have hq : 0 ≤ q := (div_pos (ht₀.trans_le ht) hτ).le
  have hq₀ : t₀/τ ≤ q := div_le_div_of_nonneg_right ht hτ.le
  let m : ℕ := Nat.floor (2*q)
  let n : ℕ := m-1
  have hmle : (m:ℝ) ≤ 2*q := Nat.floor_le (mul_nonneg (by norm_num) hq)
  have hmlt : 2*q < (m:ℝ)+1 := Nat.lt_floor_add_one (2*q)
  have hr : 0 ≤ q-(n:ℝ)/2 ∧ q-(n:ℝ)/2 < 1 ∧
      min (1/2:ℝ) (t₀/τ) ≤ q-(n:ℝ)/2 := by
    by_cases hm : m = 0
    · have hn : n = 0 := by simp only [n,hm,Nat.zero_sub]
      have hq1 : q < 1 := by
        rw [hm,Nat.cast_zero] at hmlt
        linarith only [hmlt]
      simpa only [hn,Nat.cast_zero,zero_div,sub_zero] using
        (show 0 ≤ q ∧ q < 1 ∧ min (1/2:ℝ) (t₀/τ) ≤ q from
          ⟨hq,hq1,(min_le_right _ _).trans hq₀⟩)
    · have hcast : (n:ℝ)+1 = (m:ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm))
      have hlo : (1/2:ℝ) ≤ q-(n:ℝ)/2 := by linarith only [hmle,hcast]
      have hup : q-(n:ℝ)/2 < 1 := by linarith only [hmlt,hcast]
      exact ⟨(by norm_num : (0:ℝ) ≤ 1/2).trans hlo,hup,
        (min_le_left _ _).trans hlo⟩
  let r : unitInterval := ⟨q-(n:ℝ)/2,hr.1,hr.2.1.le⟩
  refine ⟨n,r,hr.2.1,hr.2.2,?_⟩
  apply Subtype.ext
  change τ*((n:ℝ)/2+(q-(n:ℝ)/2)) = (t:ℝ)
  calc
    τ*((n:ℝ)/2+(q-(n:ℝ)/2)) = τ*q := by ring
    _ = (t:ℝ) := by dsimp only [q]; field_simp [ne_of_gt hτ]

end Lemniscate
