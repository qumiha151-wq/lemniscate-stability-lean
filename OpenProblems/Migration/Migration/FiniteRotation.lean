import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The arclength mean and convex hull of a closed profile assembled from
rotated copies of one block. The complex coordinate is relative to the
fixed similarity centre, and the parameter on the profile is arclength. -/
noncomputable section
namespace MigrationGeometry.FiniteRotation
open Set MeasureTheory
open scoped BigOperators

private theorem shifted_blocks {z : ℝ → ℂ} {P : ℝ} {w : ℂ}
    (shift : ∀ s, z (s+P) = w*z s) (j : ℕ) (s : ℝ) :
    z (s+(j:ℝ)*P) = w^j * z s := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, shift, ih, pow_succ]
    ring

/-- The arclength mean of the complete, centred profile vanishes. -/
theorem mean_eq_zero {z : ℝ → ℂ} {P : ℝ} {w : ℂ} {d : ℕ}
    (shift : ∀ s, z (s+P) = w*z s) (hw : w ≠ 1) (hd : w^d = 1) :
    ((d:ℝ)*P)⁻¹ • (∫ s in 0..((d:ℝ)*P), z s) = 0 := by
  let L := (d:ℝ)*P
  have per : Function.Periodic z L := fun s => by
    dsimp [L]
    rw [shifted_blocks shift, hd, one_mul]
  have translated := per.intervalIntegral_add_eq P 0
  have eq : w * (∫ s in 0..L, z s) = ∫ s in 0..L, z s := by
    calc
      _ = ∫ s in 0..L, w*z s := (intervalIntegral.integral_const_mul w z).symm
      _ = ∫ s in 0..L, z (s+P) := by simp only [shift]
      _ = ∫ s in (0+P)..(L+P), z s := intervalIntegral.integral_comp_add_right z P
      _ = _ := by simpa [add_comm] using translated
  have zero := (mul_eq_zero.mp (show (w-1)*(∫ s in 0..L, z s)=0 by
    rw [sub_mul, one_mul, eq, sub_self])).resolve_left (sub_ne_zero.mpr hw)
  change L⁻¹ • (∫ s in 0..L, z s) = 0
  rw [zero, smul_zero]

/-- Every translated similarity slice contains the common fixed centre
in the convex hull of its actual image over one complete period. -/
theorem center_mem_slice_hull {z : ℝ → ℂ} {P : ℝ} {w : ℂ} {d : ℕ}
    (hP : 0 < P) (hd : 0 < d) (shift : ∀ s, z (s+P) = w*z s)
    (hw : w ≠ 1) (hdw : w^d = 1) (center a : ℂ) :
    center ∈ convexHull ℝ ((fun s => center + a*z s) '' Icc 0 ((d:ℝ)*P)) := by
  let A := (fun s => center + a*z s) '' Icc 0 ((d:ℝ)*P)
  have hp (j : ℕ) (hj : j ∈ Finset.range d) :
      center + a*(w^j*z 0) ∈ convexHull ℝ A := by
    apply subset_convexHull ℝ A
    refine ⟨(j:ℝ)*P,⟨by positivity, ?_⟩, ?_⟩
    · apply mul_le_mul_of_nonneg_right _ hP.le
      exact_mod_cast (Finset.mem_range.mp hj).le
    · change center + a*z ((j:ℝ)*P) = _
      rw [show z ((j:ℝ)*P) = w^j*z 0 by simpa using shifted_blocks shift j 0]
  have dn : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hm := (convex_convexHull ℝ A).sum_mem
    (t := Finset.range d) (w := fun _ => (d:ℝ)⁻¹)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg d)) (by simp [dn]) hp
  have hsum : ∑ j ∈ Finset.range d, w^j = 0 := by rw [geom_sum_eq hw d, hdw]; simp
  have total : (∑ j ∈ Finset.range d, (center + a*(w^j*z 0))) = d • center := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hsum]
    simp
  rw [← Finset.smul_sum, total, ← Nat.cast_smul_eq_nsmul ℝ d, smul_smul, inv_mul_cancel₀ dn,
      one_smul] at hm
  exact hm

/-- A constant speed change under a similarity cancels in the arclength
mean, so it suffices here to integrate in the original unit-speed parameter. -/
theorem slice_mean_eq_center {z : ℝ → ℂ} {P : ℝ} {w : ℂ} {d : ℕ}
    (hz : Continuous z) (hP : 0 < P) (hd : 0 < d)
    (shift : ∀ s, z (s+P) = w*z s) (hw : w ≠ 1) (hdw : w^d = 1) (center a : ℂ) :
    ((d:ℝ)*P)⁻¹ • (∫ s in 0..((d:ℝ)*P), (center + a*z s)) = center := by
  let L := (d:ℝ)*P
  have hL : 0 < L := mul_pos (Nat.cast_pos.mpr hd) hP
  have hz0 : ∫ s in 0..L, z s = 0 :=
    (smul_eq_zero.mp (mean_eq_zero shift hw hdw)).resolve_left (inv_ne_zero hL.ne')
  change L⁻¹ • (∫ s in 0..L, (center + a*z s)) = center
  have hi : IntervalIntegrable (fun s : ℝ => a*z s) volume 0 L :=
    (hz.const_mul a).intervalIntegrable ..
  have hc : IntervalIntegrable (fun _ : ℝ => center) volume 0 L :=
    continuous_const.intervalIntegrable ..
  rw [intervalIntegral.integral_add hc hi, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, hz0]
  simp [hL.ne']

/-- In particular two similarity slices cannot occupy opposite open
half-planes, or any two disjoint convex sets. -/
theorem no_separated_slices {z : ℝ → ℂ} {P : ℝ} {w : ℂ} {d : ℕ}
    (hP : 0 < P) (hd : 0 < d) (shift : ∀ s, z (s+P) = w*z s)
    (hw : w ≠ 1) (hdw : w^d = 1) (center a b : ℂ)
    {A B : Set ℂ} (hA : Convex ℝ A) (hB : Convex ℝ B) (hab : Disjoint A B)
    (h₁ : (fun s => center + a*z s) '' Icc 0 ((d:ℝ)*P) ⊆ A)
    (h₂ : (fun s => center + b*z s) '' Icc 0 ((d:ℝ)*P) ⊆ B) : False :=
  Set.disjoint_left.mp hab
    ((convexHull_min h₁ hA) (center_mem_slice_hull hP hd shift hw hdw center a))
    ((convexHull_min h₂ hB) (center_mem_slice_hull hP hd shift hw hdw center b))

end MigrationGeometry.FiniteRotation

#print axioms MigrationGeometry.FiniteRotation.mean_eq_zero
#print axioms MigrationGeometry.FiniteRotation.center_mem_slice_hull
#print axioms MigrationGeometry.FiniteRotation.slice_mean_eq_center
#print axioms MigrationGeometry.FiniteRotation.no_separated_slices
