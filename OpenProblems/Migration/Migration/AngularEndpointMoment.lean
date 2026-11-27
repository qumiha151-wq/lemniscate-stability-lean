import Migration.AngularExcursionBarrier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.AngularExcursion

private theorem angle_secant {θ k : ℝ→ℝ} (dθ : ∀s,HasDerivAt θ (k s) s) (ck : Continuous k)
    {a b : ℝ} (ab : a≤b) :
    (θ b-θ a)^2 ≤ (b-a)*(∫s in a..b,(k s)^2) := by
  have cs := Flow.interval_integral_mul_sq_le (f:=fun _=>1) (g:=k) continuous_const ck ab
  simp only [one_mul,one_pow,intervalIntegral.integral_const,smul_eq_mul,mul_one] at cs
  rwa [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>dθ s) (ck.intervalIntegrable ..)] at cs

/-- A curve tangent to the horizontal at the farthest point of a half-plane
has a positive height moment, even with zero oriented area. L is the half
period in the unit-speed chart centered at that point, and h its nonnegative
distance to the comparison line. Only the two flank arcs consume energy. -/
theorem halfplane_moment {L E W : ℝ} {θ k h v : ℝ→ℝ} (ep : 0<E)
    (length : 2/E≤L) (width : 2/E≤W)
    (dθ : ∀s,HasDerivAt θ (k s) s) (ck : Continuous k) (hor : θ 0=0)
    (dh : ∀s,HasDerivAt h (v s) s) (unit : ∀s,|v s|≤1)
    (half : ∀s,0≤h s) (far : W≤h 0) (energy : (∫s in -L..L,(k s)^2)≤2*E) :
    2*W/E-4/(3*E^2) ≤ ∫s in -L..L,h s*|Real.cos (θ s)| := by
  let R := 2/E
  have r0 : 0≤R := (div_pos (by norm_num) ep).le
  have cθ := continuous_iff_continuousAt.mpr fun s => (dθ s).continuousAt
  have ch := continuous_iff_continuousAt.mpr fun s => (dh s).continuousAt
  let F := fun s=>h s * |Real.cos (θ s)|
  have cf : Continuous F := ch.mul (Real.continuous_cos.comp cθ).abs
  have dist (s : ℝ) : |h s-h 0| ≤ |s| := by
    have b := (convex_univ (𝕜:=ℝ) (E:=ℝ)).norm_image_sub_le_of_norm_deriv_le (f:=h) (C:=1)
      (fun z _=>(dh z).differentiableAt) (fun z _=>(dh z).deriv ▸ unit z) (mem_univ 0) (mem_univ s)
    simpa only [Real.norm_eq_abs,sub_zero,one_mul] using b
  have pt (r : ℝ) (hr : r∈Icc 0 R) : (W-r)*(2-r*E)≤F (-r)+F r := by
    have wn : 0≤W-r := sub_nonneg.mpr (hr.2.trans width)
    have subset := intervalIntegral.integral_mono_interval (μ:=volume) (f:=fun s=>(k s)^2)
      (neg_le_neg (hr.2.trans length)) (show -r≤r by linarith [hr.1]) (hr.2.trans length)
      (Filter.Eventually.of_forall fun s=>sq_nonneg _) ((ck.pow 2).intervalIntegrable ..)
    have two := intervalIntegral.integral_add_adjacent_intervals (f:=fun s=>(k s)^2) (μ:=volume)
      ((ck.pow 2).intervalIntegrable (-r) 0) ((ck.pow 2).intervalIntegrable 0 r)
    have all := mul_le_mul_of_nonneg_left (subset.trans energy) hr.1
    rw [←two,mul_add] at all
    have l := angle_secant dθ ck (a:=-r) (b:=0) (by linarith [hr.1])
    have u := angle_secant dθ ck hr.1
    simp only [hor,zero_sub,neg_neg,neg_sq,sub_zero] at l u
    have tangent : 2-r*E≤|Real.cos (θ (-r))|+|Real.cos (θ r)| := by
      linarith only [Real.one_sub_sq_div_two_le_cos (x:=θ (-r)),Real.one_sub_sq_div_two_le_cos (x:=θ r),
        le_abs_self (Real.cos (θ (-r))),le_abs_self (Real.cos (θ r)),l,u,all]
    have heights (s : ℝ) (hs : |s|=r) : W-r≤h s := by
      have a := (abs_le.mp (dist s)).1; rw [hs] at a; linarith only [a,far]
    have a := mul_le_mul_of_nonneg_right (heights (-r) (by rw [abs_neg,abs_of_nonneg hr.1])) (abs_nonneg (Real.cos (θ (-r))))
    have b := mul_le_mul_of_nonneg_right (heights r (abs_of_nonneg hr.1)) (abs_nonneg (Real.cos (θ r)))
    unfold F; linarith only [mul_le_mul_of_nonneg_left tangent wn,a,b]
  have funint : Continuous (fun r : ℝ=>(W-r)*(2-r*E)) := by fun_prop
  have bound := intervalIntegral.integral_mono_on (μ:=volume) r0 (funint.intervalIntegrable ..)
    (((cf.comp continuous_neg).add cf).intervalIntegrable ..) pt
  have sum : (∫ r in (0:ℝ)..R,F (-r)+F r) = ∫r in -R..R,F r := by
    rw [intervalIntegral.integral_add (f:=fun r=>F (-r)) (g:=F) ((cf.comp continuous_neg).intervalIntegrable ..)
      (cf.intervalIntegrable ..),intervalIntegral.integral_comp_neg,neg_zero,
      intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable ..) (cf.intervalIntegrable ..)]
  change (∫r in (0:ℝ)..R,(W-r)*(2-r*E)) ≤ (∫r in (0:ℝ)..R,F (-r)+F r) at bound
  rw [sum] at bound
  let primitive := fun r : ℝ=>2*W*r-(W*E+2)*r^2/2+E*r^3/3
  have dp (r : ℝ) : HasDerivAt primitive ((W-r)*(2-r*E)) r := by
    have d := hasDerivAt_id r
    apply (((d.const_mul (2*W)).sub (((d.pow 2).const_mul (W*E+2)).div_const 2)).add
      (((d.pow 3).const_mul E).div_const 3)).congr_deriv
    dsimp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _=>dp r) (funint.intervalIntegrable ..)] at bound
  have small : primitive R-primitive 0=2*W/E-4/(3*E^2) := by
    dsimp [primitive,R]; field_simp; ring
  rw [small] at bound
  exact bound.trans (intervalIntegral.integral_mono_interval (neg_le_neg length) (by linarith only [r0] : -R≤R)
    length (Filter.Eventually.of_forall fun s=>mul_nonneg (half s) (abs_nonneg _)) (cf.intervalIntegrable ..))

end MigrationGeometry.AngularExcursion
#print axioms MigrationGeometry.AngularExcursion.halfplane_moment
