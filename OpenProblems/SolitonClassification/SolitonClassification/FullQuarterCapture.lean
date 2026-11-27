import SolitonClassification.CentralReturnWindow
import SolitonClassification.CentreFastCoordinates

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.CrossingResponse
open GlobalSupport OuterStress

private theorem lab_radius {δ : ℝ} (z : Data δ) (s : ℝ) :
    z.labX z.laboratoryAngle s^2 + z.labY z.laboratoryAngle s^2 = z.p s^2 + z.q s^2 := by
  unfold Data.labX Data.labY
  linear_combination (z.p s^2+z.q s^2)*Real.sin_sq_add_cos_sq (z.laboratoryAngle s)

/-- A visit to a fixed fast-scale disk occurs within a bounded fast time.
Beyond slow time one half the positive laboratory height excludes that
disk, including the whole final arclength from the section to the seam. -/
theorem full_quarter_disk_capture (b Q : ℕ → ℝ) (bp : ∀ n, 0 < b n)
    (grow : Tendsto b atTop atTop) (positive_height : ∀ᶠ n in atTop,
      ∀ u ∈ Icc (1/2:ℝ) (Q n), b n/4800 ≤ Y (((b n)^2)⁻¹) (b n*u)) :
    ∀ R ≥ (0:ℝ), ∃ B : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) (b n * Q n),
      X (((b n)^2)⁻¹) t ^ 2 + Y (((b n)^2)⁻¹) t ^ 2 ≤ R^2 → t ≤ B := by
  intro R hR
  refine ⟨72*R+8,?_⟩
  filter_upwards [positive_height,grow.eventually (eventually_ge_atTop (32:ℝ)),
    grow.eventually (eventually_gt_atTop (4800*R))] with n height big far
  intro t ht disk
  let d := (b n)⁻¹
  let z := centreData (b n) (bp n)
  let u := t/(b n)
  have dp : 0 < d := inv_pos.mpr (bp n)
  have dt : b n * u = t := by dsimp [u]; field_simp [(bp n).ne']
  have coord := slow_fast_position (bp n) u
  dsimp only at coord
  rw [dt] at coord
  have mag : z.p u^2 + z.q u^2 ≤ (d*R)^2 := by
    rw [← lab_radius]
    change (centreData (b n) (bp n)).labX _ u ^ 2 +
      (centreData (b n) (bp n)).labY _ u ^ 2 ≤ _
    rw [coord.1,coord.2]
    dsimp only [d]
    nlinarith only [mul_le_mul_of_nonneg_left disk (sq_nonneg (b n)⁻¹)]
  have early : u ≤ 1/2 := by
    by_contra! late
    have below : u ≤ Q n := (div_le_iff₀ (bp n)).mpr (by linarith only [ht.2, mul_comm (b n) (Q n)])
    have lower := height u ⟨late.le,below⟩
    rw [dt] at lower
    have ymax : Y (((b n)^2)⁻¹) t ≤ R := by
      apply le_of_sq_le_sq _ hR
      linarith only [disk, sq_nonneg (X (((b n)^2)⁻¹) t)]
    linarith
  have init : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by
    simp [z,centreData,ofSupport,solution_zero,(bp n).ne']
  have small : d ≤ 1/32 := by
    simpa only [d,one_div] using inv_anti₀ (by norm_num : (0:ℝ)<32) big
  have res := z.fast_time_le_of_early_radius dp small init.1 init.2.1 init.2.2.1 init.2.2.2
    ⟨div_nonneg ht.1 (bp n).le,early⟩ mag hR
  simpa [u,d,div_eq_mul_inv,mul_assoc,(bp n).ne'] using res

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.full_quarter_disk_capture
