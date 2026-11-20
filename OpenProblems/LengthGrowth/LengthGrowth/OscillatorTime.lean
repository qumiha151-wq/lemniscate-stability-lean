import LengthGrowth.OscillatorClock
import LengthGrowth.OscillatorWindowMean
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Lean.Util.CollectAxioms

/-! Time averages for a global C² solution of the actual quartic Newton
equation. Periodicity, the turning points and their angular clock are derived
from the equation. -/
noncomputable section
namespace LengthGrowth.OscillatorMean
open Set Real MeasureTheory

/-- Conclusions for a nonconstant quartic trajectory. The period `4D` and
mean `N/D` are the full time integrals in turning-point coordinates. -/
structure TimeQuadrature (z : ℝ → ℝ) (c r : ℝ) : Prop where
  radius_pos : 0<r
  equal_potential : quarticPotential (c+r)=quarticPotential (c-r)
  center_pos : 0<c
  center_lt_one : c<1
  turning_plus : ∃ t∈Icc 0 (physicalPeriod c r),z t=c+r ∧ deriv z t=0
  turning_minus : ∃ t∈Icc 0 (physicalPeriod c r),z t=c-r ∧ deriv z t=0
  period_pos : 0<physicalPeriod c r
  period_le : physicalPeriod c r≤8*π
  periodic : Function.Periodic z (physicalPeriod c r)
  mean_pos : 0<periodMean c r
  mean_eq : ∀ t, (∫ x in t..t+physicalPeriod c r,z x)/physicalPeriod c r=periodMean c r
  window : ∀ {A : ℝ}, (∀ t,|z t|≤A) → ∀ s T:ℝ, 0<T →
    |(∫ t in s..s+T,z t)/T-periodMean c r|≤16*π*A/T

namespace QuarticOrbit
variable (o : QuarticOrbit)

theorem resolved_time_law : (∀ t,o.z t=1) ∨ ∃ c r : ℝ,TimeQuadrature o.z c r := by
  rcases o.equilibrium_or_turning with he|⟨c,r,hr,hp,hm⟩
  · exact Or.inl he
  have hV := hp.trans hm.symm
  obtain ⟨hc,hc',_,hd⟩ := turning_parameters hr hV
  obtain ⟨hP,hP'⟩ := period_bounds hd
  obtain ⟨per,hi,hits⟩ := o.actual_time_quadrature hr hp hm
  have hD : 0<denominator c r := by change 0<4*denominator c r at hP; linarith
  have hN (s : ℝ) : (∫ x in s..s+physicalPeriod c r,o.z x)=physicalPeriod c r*periodMean c r := by
    rw [hi]
    dsimp [physicalPeriod,periodMean]
    field_simp [hD.ne']
  obtain ⟨t,ht,et⟩ := hits 0
  obtain ⟨u,hu,eu⟩ := hits π
  simp only [anglePosition,cos_zero,mul_one] at et
  simp only [anglePosition,cos_pi,mul_neg_one,← sub_eq_add_neg] at eu
  have vel0 (x : ℝ) (he : quarticPotential (o.z x)=o.energy 0) : deriv o.z x=0 := by
    rw [(o.dz x).deriv]
    have e := o.energy_eq x
    change (o.v x)^2/2+quarticPotential (o.z x)=o.energy 0 at e
    nlinarith only [e,he]
  refine Or.inr ⟨c,r,⟨hr,hV,hc,hc',⟨t,ht,et,vel0 t (et ▸ hp)⟩,
    ⟨u,hu,eu,vel0 u (eu ▸ hm)⟩,hP,hP',per,periodMean_pos hr hV,?_,?_⟩⟩
  · intro s
    rw [hN s]
    field_simp [hP.ne']
  · intro A hA s T hT
    have cz : Continuous o.z := continuous_iff_continuousAt.mpr (fun x => (o.dz x).continuousAt)
    have h0 := hN 0
    rw [zero_add] at h0
    have hw := periodic_window_error hP cz per hA h0 s T hT
    apply hw.trans
    apply div_le_div_of_nonneg_right _ hT.le
    nlinarith only [mul_nonneg (show 0≤A from (abs_nonneg _).trans (hA 0)) (sub_nonneg.mpr hP')]

end QuarticOrbit

def QuarticOrbit.ofC2 (z : ℝ → ℝ) (hz : ContDiff ℝ 2 z)
    (eqn : ∀ t,deriv (deriv z) t=-(z t)^3/2+z t/4+1/4) : QuarticOrbit where
  z := z
  v := deriv z
  dz t := (hz.differentiable (by norm_num) t).hasDerivAt
  dv t := by
    have hz' : ContDiff ℝ 1 (deriv z) := hz.deriv'
    rw [← eqn t]
    exact (hz'.differentiable (by norm_num) t).hasDerivAt

theorem global_c2_time_quadrature (z : ℝ → ℝ) (hz : ContDiff ℝ 2 z)
    (eqn : ∀ t,deriv (deriv z) t=-(z t)^3/2+z t/4+1/4) :
    (∀ t,z t=1) ∨ ∃ c r : ℝ,TimeQuadrature z c r :=
  (QuarticOrbit.ofC2 z hz eqn).resolved_time_law

/-- A positive period mean controls every window for the equilibrium and for
each nonconstant solution, including windows shorter than one period. -/
theorem global_c2_positive_window_mean (z : ℝ → ℝ) (hz : ContDiff ℝ 2 z)
    (eqn : ∀ t,deriv (deriv z) t=-(z t)^3/2+z t/4+1/4) :
    ∃ μ : ℝ, 0<μ ∧ ∀ {A : ℝ}, (∀ t,|z t|≤A) → ∀ s T : ℝ, 0<T →
      |(∫ t in s..s+T,z t)/T-μ|≤16*π*A/T := by
  rcases global_c2_time_quadrature z hz eqn with he|⟨c,r,h⟩
  · refine ⟨1,by norm_num,?_⟩
    intro A hA s T hT
    have ha : 0≤A := (abs_nonneg _).trans (hA 0)
    rw [show z=(fun _ => (1:ℝ)) from funext he,intervalIntegral.integral_const]
    simp only [add_sub_cancel_left,smul_eq_mul,mul_one,div_self hT.ne',sub_self,abs_zero]
    positivity
  · exact ⟨periodMean c r,h.mean_pos,fun hA => h.window hA⟩

end LengthGrowth.OscillatorMean

open Lean Elab Command in
run_cmd do
  for n in #[`LengthGrowth.OscillatorMean.global_c2_time_quadrature,
             `LengthGrowth.OscillatorMean.global_c2_positive_window_mean] do
    for ax in (← collectAxioms n) do
      unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains ax do
        throwError "Unexpected axiom {ax} in {n}"
  logInfo "OSCILLATOR_TIME_AUDIT: actual global C2 orbits, attained turning points, time periods, period-mean ratios and finite-window errors."
