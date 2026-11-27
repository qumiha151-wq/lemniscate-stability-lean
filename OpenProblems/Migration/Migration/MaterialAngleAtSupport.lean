import Migration.MaterialArclength
import Migration.ProjectedHeightTransit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (c : PeriodicRegularPosition)

def label (a s : ℝ) := c.arclengthInverse (s+c.arclength a)
def kAt (a s : ℝ) := curvature c.position (c.label a s)
def angleAt (a s : ℝ) := ∫r in (0:ℝ)..s,c.kAt a r

theorem label_zero (a : ℝ) : c.label a 0=a := by simp [label,c.arclength_inverse_right]

theorem label_der (a s : ℝ) : HasDerivAt (c.label a) (speed c.position (c.label a s))⁻¹ s := by
  change HasDerivAt (fun r : ℝ=>c.arclengthInverse (r+c.arclength a)) _ s
  simpa only [label,Function.comp_def,id_eq,mul_one] using (c.inverse_hasDerivAt (s+c.arclength a)).comp s ((hasDerivAt_id s).add_const _)

theorem label_cont (a : ℝ) : Continuous (c.label a) :=
  continuous_iff_continuousAt.mpr fun s=>(c.label_der a s).continuousAt

theorem kAt_cont (a : ℝ) : Continuous (c.kAt a) :=
  (curvature_smooth c.smooth c.regular).continuous.comp (c.label_cont a)

theorem angleAt_der (a s : ℝ) : HasDerivAt (c.angleAt a) (c.kAt a s) s :=
  intervalIntegral.integral_hasDerivAt_right ((c.kAt_cont a).intervalIntegrable ..)
    ((c.kAt_cont a).stronglyMeasurableAtFilter _ _) (c.kAt_cont a).continuousAt

theorem height_der (H : ℂ→L[ℝ] ℝ) (a s : ℝ) :
    HasDerivAt (fun r=>H (c.position (c.label a r))) (H (tangent c.position (c.label a s))) s := by
  have d := H.hasFDerivAt.comp_hasDerivAt (c.label a s) (position_hasDerivAt c.smooth c.regular _)
  apply (d.comp s (c.label_der a s)).congr_deriv
  rw [map_smul,smul_eq_mul]; field_simp [(speed_pos c.regular _).ne']

theorem normal_angle (H : ℂ→L[ℝ] ℝ) (a : ℝ) (hor : H (tangent c.position a)=0)
    (s : ℝ) : H (normal c.position (c.label a s)) =
      H (normal c.position a)*Real.cos (c.angleAt a s) := by
  let U := fun r=>H (normal c.position (c.label a r))
  let V := fun r=>H (tangent c.position (c.label a r))
  let z := c.angleAt a
  have dn (r : ℝ) : HasDerivAt U (-c.kAt a r * V r) r := by
    have d := H.hasFDerivAt.comp_hasDerivAt (c.label a r) (normal_hasDerivAt c.smooth c.regular _)
    apply (d.comp r (c.label_der a r)).congr_deriv
    dsimp only [kAt,V]
    rw [←Complex.ofReal_neg,←Complex.real_smul,map_smul,smul_eq_mul]
    field_simp [(speed_pos c.regular _).ne']
  have dt (r : ℝ) : HasDerivAt V (c.kAt a r * U r) r := by
    have d := H.hasFDerivAt.comp_hasDerivAt (c.label a r) (tangent_hasDerivAt c.smooth c.regular _)
    apply (d.comp r (c.label_der a r)).congr_deriv
    dsimp only [kAt,U]
    rw [←Complex.real_smul,map_smul,smul_eq_mul]
    field_simp [(speed_pos c.regular _).ne']
  have f (r : ℝ) : HasDerivAt (fun w=>U w*Real.cos (z w)+V w*Real.sin (z w)) 0 r := by
    apply (((dn r).mul (c.angleAt_der a r).cos).add ((dt r).mul (c.angleAt_der a r).sin)).congr_deriv
    ring
  have g (r : ℝ) : HasDerivAt (fun w=>V w*Real.cos (z w)-U w*Real.sin (z w)) 0 r := by
    apply (((dt r).mul (c.angleAt_der a r).cos).sub ((dn r).mul (c.angleAt_der a r).sin)).congr_deriv
    ring
  have eqf := is_const_of_deriv_eq_zero (fun r=>(f r).differentiableAt) (fun r=>(f r).deriv) s 0
  have eqg := is_const_of_deriv_eq_zero (fun r=>(g r).differentiableAt) (fun r=>(g r).deriv) s 0
  have z0 : z 0=0 := by simp [z,angleAt]
  have U0 : U 0=H (normal c.position a) := by simp [U,c.label_zero]
  have V0 : V 0=0 := by simp [V,c.label_zero,hor]
  simp only [z0,U0,V0,Real.sin_zero,Real.cos_zero,mul_one,mul_zero,add_zero,sub_zero] at eqf eqg
  change U s=H (normal c.position a)*Real.cos (z s)
  linear_combination Real.cos (z s)*eqf -Real.sin (z s)*eqg -
    U s*(Real.sin_sq_add_cos_sq (z s))

theorem shifted_integral (a : ℝ) (f : ℝ→ℝ) (cf : Continuous f) (pf : Function.Periodic f c.period) :
    (∫s in -(c.length/2)..(c.length/2), f (c.label a s))=
      ∫u in (0:ℝ)..c.period,f u*speed c.position u := by
  let F := fun s=>f (c.arclengthInverse s)
  have per : Function.Periodic F c.length := by
    intro s; dsimp [F]; rw [c.inverse_add_length,pf _]
  change (∫s in -(c.length/2)..(c.length/2), F (s+c.arclength a))=_
  rw [intervalIntegral.integral_comp_add_right,
    show c.length/2+c.arclength a = (-(c.length/2)+c.arclength a)+c.length by ring,
    per.intervalIntegral_add_eq (-(c.length/2)+c.arclength a) 0,zero_add]
  exact c.integral_comp_inverse cf

end MigrationGeometry.Flow.PeriodicRegularPosition
