import LengthGrowth.ActualFlow.LocalizationClock

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

private theorem clock_nonneg {t : ℝ} (h : 1 ≤ t) : 0 ≤ c.localizationClock t :=
  intervalIntegral.integral_nonneg_of_forall h c.localizationDensity_nonneg

/-- The cube of the averaged physical localization clock has a finite
integral, quantitatively bounded by the loss of squared bending energy. -/
theorem localizationClock_cubic_budget (hf : c.IsNormalFEF) {t : ℝ} (ht : 1 ≤ t) :
    c.localizationClock t ^ 3 / t^2 +
      (∫ x in 1..t,(c.localizationClock x / x)^3) ≤
        33554432 * (c.energy 1 ^ 2 - c.energy t ^ 2) := by
  let g := fun x : ℝ => (c.localizationClock x / x)^3
  let W := fun x : ℝ => c.localizationClock x^3/x^2 +
    (∫ s in 1..x,g s) + 33554432*c.energy x^2
  have cg : ContinuousOn g (Ioi 0) := by
    intro x hx
    exact (((c.localizationClock_hasDerivAt x).continuousAt.div continuousAt_id
      (ne_of_gt hx)).pow 3).continuousWithinAt
  have work (x : ℝ) (hx : 1 ≤ x) : HasDerivAt W
      (3*(c.localizationClock x/x)^2*c.localizationDensity x-(c.localizationClock x/x)^3-
       67108864*c.energy x*c.dissipation x) x := by
    have xp : 0<x := by linarith
    have ig : IntervalIntegrable g volume 1 x :=
      (cg.mono (show Icc 1 x ⊆ Ioi (0:ℝ) from fun s hs => by
        change 0<s; linarith [hs.1])).intervalIntegrable_of_Icc hx
    have gx : ContinuousAt g x := cg.continuousAt (isOpen_Ioi.mem_nhds xp)
    have cb : Continuous c.localizationClock := continuous_iff_continuousAt.mpr
      (fun y => (c.localizationClock_hasDerivAt y).continuousAt)
    have gm : Measurable g := (cb.measurable.div measurable_id).pow_const 3
    have dg : HasDerivAt (fun v : ℝ => ∫ s in 1..v,g s) (g x) x :=
      intervalIntegral.integral_hasDerivAt_right ig
        gm.aestronglyMeasurable.stronglyMeasurableAtFilter gx
    have db := ((c.localizationClock_hasDerivAt x).pow 3).div
      ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 xp.ne')
    have de := ((c.energy_hasDerivAt_normal hf xp).pow 2).const_mul 33554432
    convert! (db.add dg).add de using 1
    simp only [g,Pi.pow_apply,id_eq]
    field_simp
    ring
  have dec : AntitoneOn W (Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
      (fun x hx => (work x hx).continuousAt.continuousWithinAt)
    · rw [interior_Ici]
      exact fun x hx => (work x (mem_Ioi.mp hx).le).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      have x1 := (mem_Ioi.mp hx).le
      rw [(work x x1).deriv,←show 4*c.localizationDensity x^3 =
        67108864*c.energy x*c.dissipation x by rw [c.localizationDensity_cube x1]; ring]
      have y := div_nonneg (c.clock_nonneg x1) (show 0≤x by linarith)
      have a := c.localizationDensity_nonneg x
      nlinarith only [mul_nonneg (sq_nonneg (c.localizationClock x/x-2*c.localizationDensity x)) (add_nonneg y a)]
  have result := dec (show (1:ℝ)∈Ici 1 from mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  have z : c.localizationClock 1=0 := intervalIntegral.integral_same
  dsimp only [W,g] at result
  rw [z,intervalIntegral.integral_same] at result
  linarith

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.localizationClock_cubic_budget
