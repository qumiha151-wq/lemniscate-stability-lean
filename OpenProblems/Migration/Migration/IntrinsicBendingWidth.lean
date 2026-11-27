import Migration.TrueEndpointMoment
import Migration.MaximumAreaCenter

noncomputable section
open Set MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (p:PeriodicRegularPosition)

/-- The bending on a short intrinsic arc, independently of the rest of the parameter circle. -/
def localBendingBound (r:ℝ) : Prop := ∀a:ℝ, r*(∫s in (0:ℝ)..r,(p.kAt a s)^2)≤1

private theorem local_cos (a:ℝ) {r s:ℝ} (rp:0<r) (h: p.localBendingBound r)
    (hs:s∈Icc 0 r) : 1/2≤Real.cos (p.angleAt a s) := by
  have k:=p.kAt_cont a
  have cs:=interval_integral_mul_sq_le (f:=fun _:ℝ=>1) (g:=p.kAt a) continuous_const k hs.1
  simp only [one_mul,one_pow,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at cs
  have mono:=intervalIntegral.integral_mono_interval (μ:=volume) (f:=fun u=>(p.kAt a u)^2)
    (le_refl 0) hs.1 hs.2 (Filter.Eventually.of_forall fun u=>sq_nonneg _) ((k.pow 2).intervalIntegrable ..)
  have nn:=intervalIntegral.integral_nonneg_of_forall (μ:=volume) rp.le (fun u=>sq_nonneg (p.kAt a u))
  have val:=cs.trans ((mul_le_mul_of_nonneg_left mono hs.1).trans (mul_le_mul_of_nonneg_right hs.2 nn))
  change (p.angleAt a s)^2≤_ at val
  linarith only [val,h a,Real.one_sub_sq_div_two_le_cos (x:=p.angleAt a s)]

private theorem rotated_height (e z:ℂ) :
    inner ℝ (Complex.I*e) (Complex.I*z)=inner ℝ e z := by
  rw [Complex.inner,Complex.inner]
  simp only [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.I_re,Complex.I_im]
  ring

/-- In every direction some initial arc spans at least half the intrinsic scale. -/
theorem width_of_local_bending {r:ℝ} (rp:0<r) (h:p.localBendingBound r)
    (e:ℂ) (unit:‖e‖=1) :
    ∃ x∈p.position '' Icc 0 p.period, ∃ y∈p.position '' Icc 0 p.period,
      r/2≤ inner ℝ e x-inner ℝ e y := by
  let H:=innerSL ℝ e
  let G:=innerSL ℝ (Complex.I*e)
  have gu : ‖Complex.I*e‖=1 := by simp [unit]
  have cc : Continuous (fun u=>G (p.position u)) := G.continuous.comp p.smooth.continuous
  obtain ⟨a,_,mx⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr p.period_pos.le) cc.continuousOn
  have hm : IsLocalMax (fun u=>G (p.position u)) a := by
    apply Eventually.of_forall
    intro u
    obtain ⟨z,hz,eq⟩:=p.periodic.exists_mem_Ico₀ p.period_pos u
    change G (p.position u)≤G (p.position a)
    rw [eq]; exact mx (show z∈Icc 0 p.period from ⟨hz.1,hz.2.le⟩)
  have hd : HasDerivAt (fun u=>G (p.position u)) (speed p.position a*G (tangent p.position a)) a := by
    apply (G.hasFDerivAt.comp_hasDerivAt a (position_hasDerivAt p.smooth p.regular a)).congr_deriv
    rw [map_smul,smul_eq_mul]
  have hor: G (tangent p.position a)=0 :=
    (mul_eq_zero.mp (hm.hasDerivAt_eq_zero hd)).resolve_left (speed_pos p.regular a).ne'
  let sign:=G (normal p.position a)
  have sq:sign^2=1 := by
    have ident:=SmoothPeriodicImmersion.unit_projection_identity gu (tangent p.position a)
    change (G (tangent p.position a))^2+sign^2=‖tangent p.position a‖^2 at ident
    rw [hor,tangent_unit p.regular] at ident
    linarith
  have formula (s:ℝ) : H (tangent p.position (p.label a s))=sign*Real.cos (p.angleAt a s) := by
    have idn:=p.normal_angle G a hor s
    rw [←idn]
    exact (rotated_height e _).symm
  have der (s:ℝ) : HasDerivAt (fun u=>sign*H (p.position (p.label a u)))
      (Real.cos (p.angleAt a s)) s := by
    apply ((p.height_der H a s).const_mul sign).congr_deriv
    rw [formula,←mul_assoc,show sign*sign=sign^2 by ring,sq,one_mul]
  have cosC:=Real.continuous_cos.comp (continuous_iff_continuousAt.mpr (fun s=>(p.angleAt_der a s).continuousAt))
  have cmp:=intervalIntegral.integral_mono_on (μ:=volume) rp.le (intervalIntegrable_const (c:=(1/2:ℝ)))
    (cosC.intervalIntegrable ..) (fun s hs=>p.local_cos a rp h hs)
  simp only [Function.comp_apply] at cmp
  rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>der s) (cosC.intervalIntegrable ..),p.label_zero] at cmp
  have mem (u:ℝ) : p.position u∈p.position '' Icc 0 p.period := by
    obtain ⟨z,hz,eq⟩:=p.periodic.exists_mem_Ico₀ p.period_pos u
    exact ⟨z,⟨hz.1,hz.2.le⟩,eq.symm⟩
  rcases sq_eq_one_iff.mp sq with pos|neg
  · refine ⟨_,mem (p.label a r),_,mem a,?_⟩
    change r/2≤H _-H _
    rw [pos] at cmp; linarith only [cmp]
  · refine ⟨_,mem a,_,mem (p.label a r),?_⟩
    change r/2≤H _-H _
    rw [neg] at cmp; linarith only [cmp]

end MigrationGeometry.Flow.PeriodicRegularPosition

#print axioms MigrationGeometry.Flow.PeriodicRegularPosition.width_of_local_bending
