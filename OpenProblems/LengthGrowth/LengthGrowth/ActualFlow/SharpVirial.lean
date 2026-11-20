import LengthGrowth.ActualFlow.ArclengthCoercivity
import LengthGrowth.ActualFlow.SharpWirtinger

/-! Sharp bending and dissipation inequalities for actual closed planar
curves. The dilation virial is taken about the arclength centroid. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth

namespace ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

def arclengthCentroid : ℂ := c.period⁻¹ • (∫ s in 0..c.period, c.curve s)

private theorem sharp_tangent_norm_integral : (∫ s in 0..c.period, ‖c.tangent s‖^2)=c.period := by
  simp [c.tangent_unit]

theorem sharp_energy_length : 2*Real.pi^2 ≤ c.energy*c.period := by
  let g := fun s => (c.curvature s : ℂ)*c.normal s
  have hn : Continuous c.normal := continuous_iff_continuousAt.mpr (fun s => (c.normal_deriv s).continuousAt)
  have hg : Continuous g := (Complex.continuous_ofReal.comp c.curvature_continuous).mul hn
  have h := periodic_wirtinger c.period_pos c.tangent g (by simpa using c.tangent_periodic 0)
    c.tangent_deriv hg c.tangent_integral_zero
  have hi : (∫ s in 0..c.period, ‖g s‖^2)=2*c.energy := by
    unfold energy
    rw [show ∀ z:ℝ, 2*(z/2)=z by intro z; ring]
    apply intervalIntegral.integral_congr
    intro s _
    simp [g,c.normal_unit,Real.norm_eq_abs,sq_abs]
  rw [c.sharp_tangent_norm_integral,hi] at h
  by_contra! hn
  nlinarith only [h,mul_pos c.period_pos (sub_pos.mpr hn)]

private theorem stress_inner_tangent (s : ℝ) :
    inner ℝ (c.stress s) (c.tangent s)=(c.curvature s)^2/2 := by
  have h := congrArg Complex.re (c.tangent_mul_star_stress s)
  change (c.tangent s*star (c.stress s)).re=_
  rw [h]
  norm_num [← Complex.ofReal_pow]

/-- About every fixed point, the true force paired with centered normal
support integrates to minus the bending energy. -/
theorem centered_dilation_virial (z : ℂ) :
    (∫ s in 0..c.period, c.force s*inner ℝ (c.normal s) (c.curve s-z))= -c.energy := by
  let g := fun s => c.force s*inner ℝ (c.normal s) (c.curve s-z)
  have hc : Continuous c.curve := continuous_iff_continuousAt.mpr (fun s => (c.curve_deriv s).continuousAt)
  have hn : Continuous c.normal := continuous_iff_continuousAt.mpr (fun s => (c.normal_deriv s).continuousAt)
  have hg : Continuous g := c.force_continuous.mul (hn.inner (hc.sub continuous_const))
  have hD (s : ℝ) : HasDerivAt (fun u => inner ℝ (c.stress u) (c.curve u-z))
      (g s+(c.curvature s)^2/2) s := by
    apply ((c.stress_deriv s).inner ℝ ((c.curve_deriv s).sub_const z)).congr_deriv
    rw [← Complex.real_smul,real_inner_smul_left,c.stress_inner_tangent]
    exact add_comm _ _
  have hs := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := c.period)
    (fun s _ => hD s) ((hg.add ((c.curvature_continuous.pow 2).div_const 2)).intervalIntegrable _ _)
  have hper := c.stress_periodic 0
  have hpos := c.curve_periodic 0
  simp only [zero_add] at hper hpos
  rw [hper,hpos,sub_self,intervalIntegral.integral_add (f := g) (g := fun s => c.curvature s^2/2) (hg.intervalIntegrable _ _)
    (((c.curvature_continuous.pow 2).div_const 2).intervalIntegrable _ _),intervalIntegral.integral_div] at hs
  change (∫ s in 0..c.period, g s) = -((∫ s in 0..c.period, c.curvature s^2)/2)
  linarith

theorem sharp_virial : 4*Real.pi^2*c.energy^2 ≤ c.dissipation*c.period^3 := by
  let y := fun s => c.curve s-c.arclengthCentroid
  let p := fun s => inner ℝ (c.normal s) (y s)
  have hc : Continuous c.curve := continuous_iff_continuousAt.mpr (fun s => (c.curve_deriv s).continuousAt)
  have hy : Continuous y := hc.sub continuous_const
  have hn : Continuous c.normal := continuous_iff_continuousAt.mpr (fun s => (c.normal_deriv s).continuousAt)
  have hp : Continuous p := hn.inner hy
  have hz : (∫ s in 0..c.period, y s)=0 := by
    unfold y arclengthCentroid
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const,sub_zero,smul_smul,mul_inv_cancel₀ c.period_pos.ne',one_smul,sub_self]
  have hmean := periodic_wirtinger c.period_pos y c.tangent
    (by dsimp [y]; rw [show c.curve c.period = c.curve 0 by simpa using c.curve_periodic 0])
    (fun s => (c.curve_deriv s).sub_const _) c.tangent_continuous hz
  rw [c.sharp_tangent_norm_integral] at hmean
  have hv : (∫ s in 0..c.period, c.force s*p s)= -c.energy := c.centered_dilation_virial _
  have hcs := interval_integral_mul_sq_le c.force_continuous hp c.period_pos.le
  change (∫ s in 0..c.period, c.force s*p s)^2 ≤ c.dissipation*(∫ s in 0..c.period, p s^2) at hcs
  rw [hv,neg_sq] at hcs
  have hproj : (∫ s in 0..c.period, p s^2) ≤ ∫ s in 0..c.period, ‖y s‖^2 := by
    apply intervalIntegral.integral_mono_on c.period_pos.le ((hp.pow 2).intervalIntegrable _ _)
      ((hy.norm.pow 2).intervalIntegrable _ _)
    intro s _
    have h := abs_real_inner_le_norm (c.normal s) (y s)
    rw [c.normal_unit,one_mul] at h
    change p s ^ 2 ≤ ‖y s‖^2
    rw [← sq_abs (p s)]
    exact pow_le_pow_left₀ (abs_nonneg (p s)) h 2
  have hD : 0≤c.dissipation := intervalIntegral.integral_nonneg_of_forall c.period_pos.le (fun s => sq_nonneg _)
  have h1 := hcs.trans (mul_le_mul_of_nonneg_left hproj hD)
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (2*Real.pi))
  have h3 := mul_le_mul_of_nonneg_left hmean hD
  nlinarith only [h2,h3]

end ClosedFrenetCurve

namespace ActualFlow.PeriodicRegularPosition
variable (c : PeriodicRegularPosition)

theorem material_sharp_energy_length :
    2*Real.pi^2 ≤ materialEnergy c.position c.period*materialLength c.position c.period := by
  simpa only [c.closedFrenetCurve_energy,c.closedFrenetCurve_period,length] using
    c.closedFrenetCurve.sharp_energy_length

theorem material_sharp_virial :
    4*Real.pi^2*(materialEnergy c.position c.period)^2 ≤
      materialDissipation c.position c.period*(materialLength c.position c.period)^3 := by
  simpa only [c.closedFrenetCurve_energy,c.closedFrenetCurve_dissipation,c.closedFrenetCurve_period,length] using
    c.closedFrenetCurve.sharp_virial

end ActualFlow.PeriodicRegularPosition

namespace ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem sharp_energy_length {t : ℝ} (ht : 0≤t) : 2*Real.pi^2 ≤ c.energy t*c.length t :=
  (c.regularPositionAt ht).material_sharp_energy_length

theorem sharp_virial {t : ℝ} (ht : 0≤t) : 4*Real.pi^2*(c.energy t)^2 ≤ c.dissipation t*(c.length t)^3 :=
  (c.regularPositionAt ht).material_sharp_virial

end ActualFlow.ForwardImmersion
end LengthGrowth
