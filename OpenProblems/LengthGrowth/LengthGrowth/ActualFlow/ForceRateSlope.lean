import LengthGrowth.ActualFlow.ArclengthCoercivity

noncomputable section
namespace LengthGrowth.ClosedFrenetCurve
variable (c : LengthGrowth.ClosedFrenetCurve)

/-- A pointwise bound involving only the energy and the squared elastic force. -/
theorem curvature_gradient_and_fourth_rate_bound (s : ℝ) :
    (c.curvature₁ s)^2 ≤ 16416*(c.energy*c.dissipation)^(2/3:ℝ)
        +4*c.energy^(1/4:ℝ)*c.dissipation^(3/4:ℝ) ∧
    (c.curvature s)^4 ≤ 65536*(c.energy*c.dissipation)^(2/3:ℝ) := by
  obtain ⟨z,hz,hpos,hzero,peak⟩ := c.exists_curvature_peak
  let M := |c.curvature z|
  let e := c.energy^(1/12:ℝ)
  let d := c.dissipation^(1/12:ℝ)
  have he : 0≤e := Real.rpow_nonneg c.energy_pos.le _
  have hd : 0≤d := Real.rpow_nonneg c.dissipation_nonneg _
  have hm : 0≤M := abs_nonneg _
  have power (a : ℝ) (ha : 0≤a) (n : ℕ) :
      (a^(1/12:ℝ))^n = a^((n:ℝ)/12) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ha]
    congr 1
    ring
  have e12 : e^12=c.energy := by dsimp [e]; rw [power _ c.energy_pos.le]; norm_num
  have d12 : d^12=c.dissipation := by dsimp [d]; rw [power _ c.dissipation_nonneg]; norm_num
  have m6 := c.energy_dissipation_controls_curvature z
  change (1/16777216:ℝ)*M^6 ≤ _ at m6
  have mcap : M≤16*e^2*d^2 := by
    by_contra! h
    have hp : (16*e^2*d^2)^6<M^6 := by gcongr
    rw [←e12,←d12] at m6
    nlinarith only [hp,m6]
  have droot : Real.sqrt c.dissipation=d^6 := by
    rw [←d12,show d^12=(d^6)^2 by ring,Real.sqrt_sq (by positivity)]
  have edroot : Real.sqrt (2*c.energy*c.dissipation)≤2*e^6*d^6 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [←e12,←d12]
      nlinarith only [mul_nonneg (pow_nonneg he 12) (pow_nonneg hd 12)]
  have grad := c.curvature_gradient_bound hm (fun u _ => peak u)
  have gradroot : Real.sqrt c.curvatureGradientSquare ≤ e^6*M+2*e^3*d^3 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [←e12] at grad edroot
      nlinarith only [grad,edroot, mul_nonneg (mul_nonneg (pow_nonneg he 9) hm) (pow_nonneg hd 3),
        mul_nonneg (pow_nonneg he 6) (pow_nonneg hd 6)]
  have main := (le_abs_self _).trans (c.stress_norm_sq_variation_from_peak hz hzero s)
  rw [c.stress_norm_sq,droot] at main
  change (c.curvature₁ s)^2 + (c.curvature s)^4/4 - M^4/4 ≤ _ at main
  have mult := mul_le_mul_of_nonneg_right gradroot (pow_nonneg hd 6)
  have m4 := pow_le_pow_left₀ hm mcap 4
  have mixed := mul_le_mul_of_nonneg_right mcap
    (mul_nonneg (pow_nonneg he 6) (pow_nonneg hd 6))
  have ef : e^8 = c.energy^(2/3:ℝ) := by dsimp [e]; rw [power _ c.energy_pos.le]; norm_num
  have df : d^8 = c.dissipation^(2/3:ℝ) := by dsimp [d]; rw [power _ c.dissipation_nonneg]; norm_num
  have et : e^3 = c.energy^(1/4:ℝ) := by dsimp [e]; rw [power _ c.energy_pos.le]; norm_num
  have dn : d^9 = c.dissipation^(3/4:ℝ) := by dsimp [d]; rw [power _ c.dissipation_nonneg]; norm_num
  rw [Real.mul_rpow c.energy_pos.le c.dissipation_nonneg,←ef,←df,←et,←dn]
  constructor
  · nlinarith only [main,mult,m4,mixed,sq_nonneg ((c.curvature s)^2)]
  · have hs := pow_le_pow_left₀ (abs_nonneg _) (peak s) 4
    rw [(show Even (4:ℕ) by decide).pow_abs] at hs
    change _ ≤ M^4 at hs
    nlinarith only [hs,m4]

end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.PeriodicRegularPosition
variable (p : PeriodicRegularPosition)

theorem arclength_curvature_slope (s : ℝ) :
    p.closedFrenetCurve.curvature₁ s = curvatureGradient p.position (p.arclengthInverse s) := by
  rw [←(p.closedFrenetCurve.curvature_deriv s).deriv]
  have eqf : p.closedFrenetCurve.curvature = curvature p.unitSpeedPosition := by
    funext w
    rw [p.closedFrenetCurve_curvature,p.unitSpeedPosition_curvature]
  rw [eqf,←unit_speed_curvatureGradient p.unitSpeedPosition_unit_speed]
  exact inverse_comp_curvatureGradient p.smooth p.regular p.inverse_smooth p.inverse_hasDerivAt s

theorem material_curvature_gradient_and_fourth_rate_bound (u : ℝ) :
    let E := materialEnergy p.position p.period
    let D := materialDissipation p.position p.period
    (curvatureGradient p.position u)^2 ≤ 16416*(E*D)^(2/3:ℝ)+4*E^(1/4:ℝ)*D^(3/4:ℝ) ∧
    (curvature p.position u)^4 ≤ 65536*(E*D)^(2/3:ℝ) := by
  simpa only [p.arclength_curvature_slope,p.closedFrenetCurve_curvature,
    p.arclength_inverse_right,p.closedFrenetCurve_energy,p.closedFrenetCurve_dissipation]
    using p.closedFrenetCurve.curvature_gradient_and_fourth_rate_bound (p.arclength u)
end LengthGrowth.ActualFlow.PeriodicRegularPosition

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)
theorem curvature_gradient_and_fourth_rate_bound {t : ℝ} (ht : 0≤t) (u : ℝ) :
    (curvatureGradient (c.position t) u)^2 ≤ 16416*(c.energy t*c.dissipation t)^(2/3:ℝ)
      +4*(c.energy t)^(1/4:ℝ)*(c.dissipation t)^(3/4:ℝ) ∧
    (curvature (c.position t) u)^4 ≤ 65536*(c.energy t*c.dissipation t)^(2/3:ℝ) :=
  (c.regularPositionAt ht).material_curvature_gradient_and_fourth_rate_bound u
end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ClosedFrenetCurve.curvature_gradient_and_fourth_rate_bound
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.arclength_curvature_slope
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.curvature_gradient_and_fourth_rate_bound
