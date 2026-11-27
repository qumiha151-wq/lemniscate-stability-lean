import LengthGrowth.ActualFlow.NodalSlopeRate
import LengthGrowth.ActualFlow.ForcePersistence
noncomputable section
open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

def curvatureSign (s : ℝ) := if 0≤c.curvature s then (1:ℝ) else -1
def signedNodalMass : ℝ := (∫s in 0..c.period, |c.curvature s|^3)/4 -
  (∫s in 0..c.period,c.curvatureSign s*c.force s)/2

private theorem signedForceIntegrable :
    IntervalIntegrable (fun s=>c.curvatureSign s*c.force s) volume 0 c.period := by
  classical
  let B := {s | 0≤c.curvature s}
  have f := intervalIntegrable_iff.mp (c.force_continuous.intervalIntegrable (μ:=volume) 0 c.period)
  have d : (fun s=>c.curvatureSign s*c.force s)=B.piecewise c.force (-c.force) := by
    funext s
    by_cases h : 0≤c.curvature s <;> simp [curvatureSign,B,Set.piecewise,h]
  rw [d,intervalIntegrable_iff]
  exact Integrable.piecewise ((isClosed_le continuous_const c.curvature_continuous).measurableSet)
    f.integrableOn f.neg.integrableOn

/-- Exact three-deficit expansion for a closed arclength slice. -/
theorem nodal_square_formula {a m : ℝ} (ap : 0<a) (mp : 0<m)
    (aa : a^2*c.period=c.dissipation) (mm : m^2*c.period=2*c.energy) :
    c.energy*(∫s in 0..c.period,c.curvature s*c.force s)-c.period*c.dissipation =
    2*a*c.period*c.signedNodalMass -
    (a*c.period/2)*(∫s in 0..c.period,(|c.curvature s|-m)^2*(|c.curvature s|+m/2)) -
    (c.period/2)*(∫s in 0..c.period,(c.force s-a*c.curvatureSign s)^2) -
    (c.energy*m/(2*a))*(∫s in 0..c.period,(c.force s-(a/m)*c.curvature s)^2) := by
  have ck := c.curvature_continuous
  have cf := c.force_continuous
  have cu := c.signedForceIntegrable
  have f2 : (∫s in 0..c.period,c.force s^2)=c.dissipation := rfl
  have k2 : (∫s in 0..c.period,c.curvature s^2)=2*c.energy := by unfold energy; ring
  have variance : (∫s in 0..c.period,(|c.curvature s|-m)^2*(|c.curvature s|+m/2))=
      (∫s in 0..c.period,|c.curvature s|^3)-(3*m/2)*(2*c.energy)+(m^3/2)*c.period := by
    have pt (s : ℝ) : (|c.curvature s|-m)^2*(|c.curvature s|+m/2)=
      (|c.curvature s|^3-(3*m/2)*c.curvature s^2)+m^3/2 := by
      rw [← sq_abs (c.curvature s)]; ring
    simp_rw [pt]
    rw [intervalIntegral.integral_add (f:=fun s=>|c.curvature s|^3-(3*m/2)*c.curvature s^2)
      (g:=fun _=>m^3/2) (((ck.abs.pow 3).sub ((ck.pow 2).const_mul _)).intervalIntegrable ..) intervalIntegrable_const,
      intervalIntegral.integral_sub (f:=fun s=>|c.curvature s|^3) (g:=fun s=>(3*m/2)*c.curvature s^2)
        ((ck.abs.pow 3).intervalIntegrable ..) (((ck.pow 2).const_mul _).intervalIntegrable ..),
      intervalIntegral.integral_const_mul,k2,intervalIntegral.integral_const, sub_zero,smul_eq_mul,mul_comm c.period]
  have sf : (∫s in 0..c.period,(c.force s-a*c.curvatureSign s)^2)=c.dissipation-
      2*a*(∫s in 0..c.period,c.curvatureSign s*c.force s)+a^2*c.period := by
    have eq (s : ℝ) : (c.force s-a*c.curvatureSign s)^2=
        (c.force s^2-(2*a)*(c.curvatureSign s*c.force s))+a^2 := by
      unfold curvatureSign; split <;> ring
    simp_rw [eq]
    rw [intervalIntegral.integral_add (f:=fun s=>c.force s^2-(2*a)*(c.curvatureSign s*c.force s))
      (g:=fun _=>a^2) (((cf.pow 2).intervalIntegrable ..).sub (cu.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub (f:=fun s=>c.force s^2) (g:=fun s=>(2*a)*(c.curvatureSign s*c.force s))
        ((cf.pow 2).intervalIntegrable ..) (cu.const_mul _), f2,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, sub_zero,smul_eq_mul,mul_comm c.period]
  have kf : (∫s in 0..c.period,(c.force s-(a/m)*c.curvature s)^2)=c.dissipation-
      2*(a/m)*(∫s in 0..c.period,c.curvature s*c.force s)+(a/m)^2*(2*c.energy) := by
    have eq (s : ℝ) : (c.force s-(a/m)*c.curvature s)^2=
        (c.force s^2-(2*(a/m))*(c.curvature s*c.force s))+(a/m)^2*c.curvature s^2 := by ring
    simp_rw [eq]
    rw [intervalIntegral.integral_add (f:=fun s=>c.force s^2-(2*(a/m))*(c.curvature s*c.force s))
      (g:=fun s=>(a/m)^2*c.curvature s^2)
      (((cf.pow 2).sub ((ck.mul cf).const_mul _)).intervalIntegrable ..)
      (((ck.pow 2).const_mul _).intervalIntegrable ..),
      intervalIntegral.integral_sub (f:=fun s=>c.force s^2) (g:=fun s=>(2*(a/m))*(c.curvature s*c.force s))
        ((cf.pow 2).intervalIntegrable ..) (((ck.mul cf).const_mul _).intervalIntegrable ..),
      f2,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,k2]
  rw [variance,sf,kf,signedNodalMass,←aa,show c.energy=m^2*c.period/2 by linarith only [mm]]
  field_simp [ap.ne',mp.ne']
  ring
end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.nodal_square_formula
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Signed-moment expression for twice the inflection slope feed, with the
nonnegative part explicit to make the infinite-time criterion independent
of any separate claim about the structure of the curvature zero set. -/
def nodalSquareAllowance (t : ℝ) : ℝ := if ht : 0≤t then
  2*Real.sqrt (c.dissipation t/c.length t)*c.length t*
    max 0 ((c.regularPositionAt ht).closedFrenetCurve.signedNodalMass) else 0

theorem deriv_product_le_nodalSquareAllowance (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t) :
    deriv c.normalizedProduct t ≤ c.nodalSquareAllowance t := by
  let c₀ := c.regularPositionAt ht.le
  let p := c₀.closedFrenetCurve
  let a := Real.sqrt (c.dissipation t/c.length t)
  let m := Real.sqrt (2*c.energy t/c.length t)
  have he : p.energy=c.energy t := c₀.closedFrenetCurve_energy
  have hd : p.dissipation=c.dissipation t := c₀.closedFrenetCurve_dissipation
  have hl : p.period=c.length t := rfl
  have lpos := c.length_pos ht.le
  have epos := c.energy_pos ht.le
  have dpos := c.force_dissipation_pos ht.le
  have ap : 0<a := Real.sqrt_pos.mpr (div_pos dpos lpos)
  have mp : 0<m := Real.sqrt_pos.mpr (by positivity)
  have aa : a^2*p.period=p.dissipation := by
    dsimp only [a]; rw [Real.sq_sqrt (by positivity),hl,hd,div_mul_cancel₀ _ lpos.ne']
  have mm : m^2*p.period=2*p.energy := by
    dsimp only [m]; rw [Real.sq_sqrt (by positivity),hl,he,div_mul_cancel₀ _ lpos.ne']
  have sq := p.nodal_square_formula ap mp aa mm
  have g₁ := intervalIntegral.integral_nonneg_of_forall (μ:=volume) p.period_pos.le
    (fun s=> mul_nonneg (sq_nonneg (|p.curvature s|-m)) (show 0≤|p.curvature s|+m/2 by positivity))
  have g₂ := intervalIntegral.integral_nonneg_of_forall (μ:=volume) p.period_pos.le
    (fun s=>sq_nonneg (p.force s-a*p.curvatureSign s))
  have g₃ := intervalIntegral.integral_nonneg_of_forall (μ:=volume) p.period_pos.le
    (fun s=>sq_nonneg (p.force s-(a/m)*p.curvature s))
  have phys : (∫s in 0..p.period,p.curvature s*p.force s)=c.lengthRate t := c₀.arclength_integral_curvature_force
  have plpos := p.period_pos
  have pepos := p.energy_pos
  have bound := calc
    p.energy*(∫s in 0..p.period,p.curvature s*p.force s)-p.period*p.dissipation
        ≤ 2*a*p.period*p.signedNodalMass := by
          linarith only [sq,mul_nonneg (show 0≤a*p.period/2 by positivity) g₁,
            mul_nonneg (show 0≤p.period/2 by positivity) g₂,
            mul_nonneg (show 0≤p.energy*m/(2*a) by positivity) g₃]
    _ ≤ 2*a*p.period*max 0 p.signedNodalMass := mul_le_mul_of_nonneg_left (le_max_right ..) (by positivity)
  rw [nodalSquareAllowance,dif_pos ht.le,(c.normalizedProduct_hasDerivAt_normal hf ht).deriv]
  rw [phys,he,hl,hd] at bound
  exact bound

theorem quarter_bounds_of_integrable_nodalSquareAllowance (hf : c.IsNormalFEF) {T : ℝ}
    (tp : 0<T) (hi : IntegrableOn c.nodalSquareAllowance (Ici T)) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound := by
  apply c.quarter_bounds_of_integrable_rate_majorant hf tp _ _ hi
    (fun _ h=>c.deriv_product_le_nodalSquareAllowance hf (tp.trans_le h))
  intro t
  unfold nodalSquareAllowance
  split
  next h =>
    have l := c.length_pos h
    positivity
  next => exact le_rfl

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_bounds_of_integrable_nodalSquareAllowance
