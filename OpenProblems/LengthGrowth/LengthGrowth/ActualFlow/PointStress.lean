import LengthGrowth.ActualFlow.SharpVirial
import LengthGrowth.ActualFlow.ForwardDissipation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp

noncomputable section
open MeasureTheory Set

namespace LengthGrowth.ClosedFrenetCurve

variable (c : ClosedFrenetCurve)

/-- The vector mean of the elastic stress is controlled by bending energy. -/
theorem integral_stress_norm_bound :
    ‖∫ u in 0..c.period, c.stress u‖ ≤ 3*c.energy := by
  let y := fun u => (3/2:ℂ)*(c.curvature u:ℂ)^2*c.tangent u
  have cy : Continuous y :=
    (continuous_const.mul ((Complex.continuous_ofReal.comp c.curvature_continuous).pow 2)).mul
      c.tangent_continuous
  have d (u : ℝ) : HasDerivAt (fun x => (c.curvature x:ℂ)*c.normal x)
      (c.stress u-y u) u := by
    apply (((c.curvature_deriv u).ofReal_comp).mul (c.normal_deriv u)).congr_deriv
    dsimp [stress,y]
    ring
  have intd := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun u _ => d u) ((c.stress_continuous.sub cy).intervalIntegrable _ _)
  have kp : c.curvature c.period = c.curvature 0 := by simpa using c.curvature_periodic 0
  have np : c.normal c.period = c.normal 0 := by
    dsimp [normal]
    rw [show c.tangent c.period=c.tangent 0 by simpa using c.tangent_periodic 0]
  rw [kp,np,sub_self,intervalIntegral.integral_sub
    (c.stress_continuous.intervalIntegrable _ _) (cy.intervalIntegrable _ _)] at intd
  rw [sub_eq_zero.mp intd]
  calc
    _ ≤ ∫ u in 0..c.period, ‖y u‖ :=
      intervalIntegral.norm_integral_le_integral_norm c.period_pos.le
    _ = ∫ u in 0..c.period, (3/2:ℝ)*c.curvature u^2 := by
      apply intervalIntegral.integral_congr
      intro u _
      simp only [y,norm_mul,norm_pow,c.tangent_unit,mul_one,Complex.norm_real,
        Real.norm_eq_abs,sq_abs,norm_div]
      norm_num
    _ = _ := by rw [intervalIntegral.integral_const_mul]; unfold energy; ring

/-- The sharp one-dimensional mean-subtraction kernel on a period. -/
private theorem square_linear_kernel (s L : ℝ) :
    (∫ u in s..s+L, (u-s-L/2)^2)=L^3/12 := by
  have h (u : ℝ) : HasDerivAt (fun x : ℝ => (x-s-L/2)^3/3) ((u-s-L/2)^2) u := by
    apply (((((hasDerivAt_id u).sub_const s).sub_const (L/2)).pow 3).div_const 3).congr_deriv
    simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => h u)
    (((continuous_id.sub continuous_const).sub continuous_const).pow 2 |>.intervalIntegrable _ _)]
  ring

/-- An actual closed curve at an arbitrary marked arclength, with no sign
    condition on the length velocity. -/
theorem point_stress_bound (s : ℝ) :
    ‖c.stress s‖ ≤ (3/(2*Real.pi)+1/Real.sqrt 12)*Real.sqrt (c.period*c.dissipation) := by
  let L := c.period
  let w := fun u : ℝ => u-s-L/2
  let f := fun u : ℝ => (w u:ℂ)*((c.force u:ℂ)*c.normal u)
  have lp : 0<L := c.period_pos
  have cw : Continuous w := (continuous_id.sub continuous_const).sub continuous_const
  have cn : Continuous c.normal :=
    continuous_iff_continuousAt.mpr fun u => (c.normal_deriv u).continuousAt
  have cf : Continuous f := (Complex.continuous_ofReal.comp cw).mul
    ((Complex.continuous_ofReal.comp c.force_continuous).mul cn)
  have dw (u : ℝ) : HasDerivAt w 1 u :=
    ((hasDerivAt_id u).sub_const s).sub_const (L/2)
  have h (u : ℝ) : HasDerivAt (fun x => (w x:ℂ)*c.stress x)
      (c.stress u + f u) u := by
    apply (((dw u).ofReal_comp).mul (c.stress_deriv u)).congr_deriv
    simp [f]
  have ibp := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=s) (b:=s+L)
    (fun u _ => h u) ((c.stress_continuous.add cf).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (c.stress_continuous.intervalIntegrable _ _)
    (cf.intervalIntegrable _ _),c.stress_periodic s] at ibp
  have bd : (w (s+L):ℂ)*c.stress s-(w s:ℂ)*c.stress s=(L:ℂ)*c.stress s := by
    dsimp [w]; push_cast; ring
  rw [bd,c.stress_periodic.intervalIntegral_add_eq s 0,zero_add] at ibp
  have pf : Function.Periodic (fun u => c.force u^2) L := by
    intro u
    have dp := LengthGrowth.periodic_actual_deriv c.curvature₁_periodic
      (fun v => (c.curvature₁_deriv v).differentiableAt) u
    rw [(c.curvature₁_deriv _).deriv,(c.curvature₁_deriv _).deriv] at dp
    dsimp [force,L]
    rw [dp,c.curvature_periodic u]
  have hs : s≤s+L := by linarith
  have bound : ‖∫ u in s..s+L, f u‖ ≤ Real.sqrt (L^3/12)*Real.sqrt c.dissipation := by
    calc
      _ ≤ ∫ u in s..s+L, ‖f u‖ := intervalIntegral.norm_integral_le_integral_norm hs
      _ = ∫ u in s..s+L, |w u*c.force u| := by
        apply intervalIntegral.integral_congr
        intro u _
        simp [f,c.normal_unit,abs_mul]
      _ ≤ _ := by
        have b := LengthGrowth.interval_integral_abs_mul_le cw c.force_continuous hs
        rw [show (∫ u in s..s+L, w u^2)=L^3/12 from square_linear_kernel s L,
          pf.intervalIntegral_add_eq s 0,zero_add] at b
        exact b
  have hb := (norm_add_le (∫ u in 0..c.period, c.stress u) (∫ u in s..s+L, f u)).trans
    (add_le_add c.integral_stress_norm_bound bound)
  rw [ibp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos lp] at hb
  let d := Real.sqrt (L*c.dissipation)
  have d0 : 0≤d := Real.sqrt_nonneg _
  have d2 : d^2=L*c.dissipation := Real.sq_sqrt (mul_nonneg lp.le c.dissipation_nonneg)
  have v := c.sharp_virial
  change 4*Real.pi^2*c.energy^2≤c.dissipation*L^3 at v
  have el : 2*Real.pi*c.energy ≤ L*d := by
    apply le_of_sq_le_sq _ (mul_nonneg lp.le d0)
    nlinarith only [v,congrArg (fun x => L^2*x) d2]
  have pi0 := Real.pi_pos
  have term : Real.sqrt (L^3/12)*Real.sqrt c.dissipation=L*d/Real.sqrt 12 := by
    apply le_antisymm <;> apply le_of_sq_le_sq <;> try positivity
    all_goals
      rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt c.dissipation_nonneg,
        div_pow,mul_pow,d2,Real.sq_sqrt (by norm_num : (0:ℝ)≤12)]
      ring_nf
      rfl
  rw [term] at hb
  change ‖c.stress s‖ ≤ (3/(2*Real.pi)+1/Real.sqrt 12)*d
  apply (le_of_mul_le_mul_left (a:=L) _ lp)
  have e : 3*c.energy ≤ (3/(2*Real.pi))*(L*d) := by
    field_simp [pi0.ne']
    linarith
  linarith only [hb,e,show L*((3/(2*Real.pi)+1/Real.sqrt 12)*d) =
    (3/(2*Real.pi))*(L*d)+L*d/Real.sqrt 12 by ring]

/-- The coefficient-one homothety law on the actual position identifies its
    elastic dissipation with its bending energy. -/
theorem actual_homothetic_dissipation {z : ℂ}
    (law : ∀ u, c.force u = -inner ℝ (c.normal u) (c.curve u-z)) :
    c.dissipation=c.energy := by
  have h := c.centered_dilation_virial z
  have he : (∫ u in 0..c.period, c.force u*inner ℝ (c.normal u) (c.curve u-z)) =
      -(∫ u in 0..c.period, c.force u^2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    change c.force u*inner ℝ (c.normal u) (c.curve u-z) = -(c.force u)^2
    rw [law u]
    ring
  rw [he] at h
  exact neg_inj.mp h

/-- Every full geometric period of a coefficient-one pure expander bounds
    every actual curvature derivative, including its value at an inflection. -/
theorem homothetic_slope_product_and_length {z : ℂ}
    (law : ∀ u, c.force u = -inner ℝ (c.normal u) (c.curve u-z)) (s : ℝ) :
    (c.curvature₁ s)^2 ≤ (3/(2*Real.pi)+1/Real.sqrt 12)^2*(c.energy*c.period) ∧
    2*Real.pi*|c.curvature₁ s| ≤ (3/(2*Real.pi)+1/Real.sqrt 12)*c.period^2 := by
  let C := 3/(2*Real.pi)+1/Real.sqrt 12
  have cp : 0<C := by dsimp [C]; positivity
  have de := c.actual_homothetic_dissipation law
  have h := c.point_stress_bound s
  rw [de,mul_comm c.period] at h
  have sm : |c.curvature₁ s|≤‖c.stress s‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [c.stress_norm_sq,sq_abs]
    nlinarith only [sq_nonneg ((c.curvature s)^2)]
  have hmark : |c.curvature₁ s| ≤ C*Real.sqrt (c.energy*c.period) := sm.trans h
  have r2 := Real.sq_sqrt (mul_nonneg c.energy_pos.le c.period_pos.le)
  have first := pow_le_pow_left₀ (abs_nonneg _) hmark 2
  rw [sq_abs,mul_pow,r2] at first
  refine ⟨first,?_⟩
  have vir := c.sharp_virial
  rw [de] at vir
  have e : 4*Real.pi^2*c.energy ≤ c.period^3 := by
    apply le_of_mul_le_mul_left (a:=c.energy) _ c.energy_pos
    nlinarith only [vir]
  have sr : 2*Real.pi*Real.sqrt (c.energy*c.period) ≤ c.period^2 := by
    apply le_of_sq_le_sq _ (sq_nonneg _)
    nlinarith only [mul_le_mul_of_nonneg_right e c.period_pos.le,
      congrArg (fun x => 4*Real.pi^2*x) r2]
  calc
    _ ≤ (2*Real.pi)*(C*Real.sqrt (c.energy*c.period)) :=
      mul_le_mul_of_nonneg_left hmark (by positivity)
    _ = C*(2*Real.pi*Real.sqrt (c.energy*c.period)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left sr cp.le

end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- A trace of arbitrary nonnegative measured stresses along a true flow.
    The realizing arclength point may change independently at every time. -/
theorem integrated_stress_cost (hf : c.IsNormalFEF) {s t : ℝ}
    (hs : 0≤s) (hst : s≤t) (m : ℝ → ℝ)
    (hi : IntervalIntegrable (fun x => (m x)^2/c.length x) volume s t)
    (marks : ∀ x, ∀ hx : x∈Icc s t, ∃ u : ℝ,
      0≤m x ∧ m x≤‖(c.regularPositionAt (hs.trans hx.1)).closedFrenetCurve.stress u‖) :
    (∫ x in s..t, (m x)^2/c.length x) ≤
      (3/(2*Real.pi)+1/Real.sqrt 12)^2*(c.energy s-c.energy t) := by
  let C := 3/(2*Real.pi)+1/Real.sqrt 12
  have hc := c.dissipation_continuousOn.mono (show Icc s t ⊆ Ici 0 from
    fun x hx => hs.trans hx.1)
  have mono : (∫ x in s..t, (m x)^2/c.length x) ≤ ∫ x in s..t, C^2*c.dissipation x := by
    apply intervalIntegral.integral_mono_on hst hi
      ((continuousOn_const.mul hc).intervalIntegrable_of_Icc hst)
    intro x hx
    have x0 := hs.trans hx.1
    let p := c.regularPositionAt x0
    have xl : 0<c.length x := p.length_pos
    obtain ⟨u,hm,hp⟩ := marks x hx
    have h := p.closedFrenetCurve.point_stress_bound u
    rw [p.closedFrenetCurve_period,p.closedFrenetCurve_dissipation] at h
    change ‖p.closedFrenetCurve.stress u‖≤C*Real.sqrt (c.length x*c.dissipation x) at h
    have hh := pow_le_pow_left₀ hm (hp.trans h) 2
    rw [mul_pow,Real.sq_sqrt (mul_nonneg xl.le (c.dissipation_nonneg x))] at hh
    apply (div_le_iff₀ xl).mpr
    change (m x)^2≤C^2*c.dissipation x*c.length x
    simpa only [mul_comm (c.length x),mul_assoc] using hh
  rw [intervalIntegral.integral_const_mul] at mono
  have h := c.energy_add_integral_dissipation hf hs hst
  rw [show (∫ x in s..t, c.dissipation x)=c.energy s-c.energy t by linarith] at mono
  exact mono

end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ClosedFrenetCurve.point_stress_bound
#print axioms LengthGrowth.ClosedFrenetCurve.homothetic_slope_product_and_length
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.integrated_stress_cost

