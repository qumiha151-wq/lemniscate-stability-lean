import LengthGrowth.ActualFlow.ForceAngularSpeed

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

def exponentialMass (l : ℂ →L[ℝ] ℝ) (a : ℝ) : ℝ :=
  ∫ s in 0..c.period, Real.exp (a*l (c.curve s))*(c.curvature s^2/2+a^2)

/-- A fixed length of the curve next to any geometric point detects its position
in an exponential moment, including when the entire curve is far from the origin. -/
theorem exponentialMass_detects_position (l : ℂ →L[ℝ] ℝ) (hl : ∀z, |l z| ≤ ‖z‖)
    {a m : ℝ} (ha : 0≤a) (hm : 0≤m) (hP : m≤c.period) (s : ℝ) :
    m*a^2*Real.exp (a*(l (c.curve s)-m)) ≤ c.exponentialMass l a := by
  let f := fun x => Real.exp (a*l (c.curve x))*(c.curvature x^2/2+a^2)
  have cx : Continuous c.curve := continuous_iff_continuousAt.mpr fun x => (c.curve_deriv x).continuousAt
  have cf : Continuous f := ((l.continuous.comp cx).const_mul a).rexp.mul
    (((c.curvature_continuous.pow 2).div_const 2).add continuous_const)
  have fp : Function.Periodic f c.period := by
    intro x
    simp only [f,c.curve_periodic x,c.curvature_periodic x]
  have fn (x : ℝ) : 0≤f x := by dsimp [f]; positivity
  have sm : s≤s+m := by linarith
  have sub := intervalIntegral.integral_mono_interval (μ:=volume) (le_refl s) sm
    (show s+m≤s+c.period by linarith) (Filter.Eventually.of_forall fn) (cf.intervalIntegrable _ _)
  rw [fp.intervalIntegral_add_eq s 0, zero_add] at sub
  have loc : ∀x∈Icc s (s+m), a^2*Real.exp (a*(l (c.curve s)-m)) ≤ f x := by
    intro x hx
    have o := LengthGrowth.interval_oscillation_le c.curve_deriv c.tangent_continuous
      (show x∈Icc s (s+m) from hx) (show s∈Icc s (s+m) from ⟨le_rfl,sm⟩)
    simp only [c.tangent_unit,intervalIntegral.integral_const,smul_eq_mul,mul_one,
      add_sub_cancel_left] at o
    have co := (hl (c.curve x-c.curve s)).trans o
    rw [map_sub] at co
    have hlow : l (c.curve s)-m≤l (c.curve x) := by linarith only [(abs_le.mp co).1]
    have e := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlow ha)
    dsimp only [f]
    rw [mul_comm (a^2)]
    exact mul_le_mul e (by nlinarith only [sq_nonneg (c.curvature x)] ) (sq_nonneg _) (Real.exp_pos _).le
  have lb := intervalIntegral.integral_mono_on (μ:=volume) sm (intervalIntegrable_const)
    (cf.intervalIntegrable _ _) loc
  simpa [exponentialMass,f,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using lb.trans sub

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.exponentialMass_detects_position
