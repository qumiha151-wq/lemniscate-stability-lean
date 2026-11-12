import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Elastic stress of a genuine closed unit-speed planar curve

The plane is `ℂ`, viewed as a real normed space. The data contain an actual
closed curve and its Frenet derivatives. No stress identity, force bound,
or coercivity estimate is assumed. This is the geometric foundation of
the independent LengthGrowth proof; the quantitative coercivity theorem
is not yet included in this initial module.
-/

noncomputable section
open MeasureTheory Set
open scoped Interval ComplexConjugate

namespace LengthGrowth

structure ClosedFrenetCurve where
  period : ℝ
  period_pos : 0 < period
  curve : ℝ → ℂ
  tangent : ℝ → ℂ
  curvature : ℝ → ℝ
  curvature₁ : ℝ → ℝ
  curvature₂ : ℝ → ℝ
  curve_periodic : Function.Periodic curve period
  tangent_periodic : Function.Periodic tangent period
  curvature_periodic : Function.Periodic curvature period
  curvature₁_periodic : Function.Periodic curvature₁ period
  curve_deriv : ∀ s, HasDerivAt curve (tangent s) s
  tangent_deriv : ∀ s, HasDerivAt tangent
    ((curvature s : ℂ) * (Complex.I * tangent s)) s
  curvature_deriv : ∀ s, HasDerivAt curvature (curvature₁ s) s
  curvature₁_deriv : ∀ s, HasDerivAt curvature₁ (curvature₂ s) s
  curvature₂_continuous : Continuous curvature₂
  tangent_unit : ∀ s, ‖tangent s‖ = 1

namespace ClosedFrenetCurve

variable (c : ClosedFrenetCurve)

def normal (s : ℝ) : ℂ := Complex.I * c.tangent s
def force (s : ℝ) : ℝ := c.curvature₂ s + c.curvature s ^ 3 / 2
def stress (s : ℝ) : ℂ :=
  ((c.curvature s : ℂ) ^ 2 / 2) * c.tangent s +
    (c.curvature₁ s : ℂ) * c.normal s
def invertedStress (s : ℝ) : ℂ := (star (c.stress s))⁻¹
def invertedStressDerivative (s : ℝ) : ℂ :=
  -star ((c.force s : ℂ) * c.normal s) / star (c.stress s) ^ 2

theorem tangent_continuous : Continuous c.tangent :=
  continuous_iff_continuousAt.mpr fun s => (c.tangent_deriv s).continuousAt

theorem curvature_continuous : Continuous c.curvature :=
  continuous_iff_continuousAt.mpr fun s => (c.curvature_deriv s).continuousAt

theorem curvature₁_continuous : Continuous c.curvature₁ :=
  continuous_iff_continuousAt.mpr fun s => (c.curvature₁_deriv s).continuousAt

theorem normal_deriv (s : ℝ) :
    HasDerivAt c.normal (-(c.curvature s : ℂ) * c.tangent s) s := by
  convert! (c.tangent_deriv s).const_mul Complex.I using 1
  calc
    _ = (Complex.I * Complex.I) * ((c.curvature s : ℂ) * c.tangent s) := by
      rw [Complex.I_mul_I]; ring
    _ = _ := by ring

theorem normal_unit (s : ℝ) : ‖c.normal s‖ = 1 := by
  simp [normal, c.tangent_unit]

theorem force_continuous : Continuous c.force := by
  exact c.curvature₂_continuous.add ((c.curvature_continuous.pow 3).div_const 2)

theorem stress_deriv (s : ℝ) :
    HasDerivAt c.stress ((c.force s : ℂ) * c.normal s) s := by
  have hk := (c.curvature_deriv s).ofReal_comp
  have hk₁ := (c.curvature₁_deriv s).ofReal_comp
  convert! (((hk.mul hk).div_const 2).mul (c.tangent_deriv s)).add
    (hk₁.mul (c.normal_deriv s)) using 1
  · funext x
    simp [stress, pow_two]
  · simp only [force, normal, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_ofNat, Pi.mul_apply]
    ring

theorem stress_continuous : Continuous c.stress :=
  continuous_iff_continuousAt.mpr fun s => (c.stress_deriv s).continuousAt

theorem tangent_integral_zero : (∫ s in 0..c.period, c.tangent s) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => c.curve_deriv s) (c.tangent_continuous.intervalIntegrable _ _)]
  have h := c.curve_periodic 0
  simpa using sub_eq_zero.mpr (by simpa using h)

theorem stress_factor (s : ℝ) : c.stress s =
    ((c.curvature s : ℂ)^2 / 2 + (c.curvature₁ s : ℂ) * Complex.I) *
      c.tangent s := by
  dsimp [stress, normal]
  ring

theorem stress_norm_sq (s : ℝ) :
    ‖c.stress s‖^2 = c.curvature₁ s ^ 2 + c.curvature s ^ 4 / 4 := by
  rw [← Complex.normSq_eq_norm_sq, c.stress_factor, Complex.normSq_mul]
  have ht : Complex.normSq (c.tangent s) = 1 := by
    simp [Complex.normSq_eq_norm_sq, c.tangent_unit]
  rw [ht, mul_one]
  have ha := Complex.normSq_add_mul_I (c.curvature s ^ 2 / 2) (c.curvature₁ s)
  simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat] at ha
  rw [ha]
  ring

theorem stress_norm_sq_deriv (s : ℝ) :
    HasDerivAt (fun u => ‖c.stress u‖^2)
      (2 * c.curvature₁ s * c.force s) s := by
  have h := ((c.curvature₁_deriv s).pow 2).add
    (((c.curvature_deriv s).pow 4).div_const 4)
  convert! h using 1
  · funext u
    exact c.stress_norm_sq u
  · dsimp [force]
    ring

theorem tangent_mul_star (s : ℝ) :
    c.tangent s * star (c.tangent s) = 1 := by
  change c.tangent s * conj (c.tangent s) = 1
  rw [Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, c.tangent_unit]

theorem tangent_mul_star_stress (s : ℝ) :
    c.tangent s * star (c.stress s) =
      (c.curvature s : ℂ)^2 / 2 - (c.curvature₁ s : ℂ) * Complex.I := by
  change c.tangent s * conj (c.stress s) = _
  rw [c.stress_factor]
  simp only [map_mul, map_add, map_div₀, map_pow, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  calc
    _ = ((c.curvature s : ℂ)^2 / 2 - (c.curvature₁ s : ℂ) * Complex.I) *
        (c.tangent s * conj (c.tangent s)) := by ring
    _ = _ := by
      have h := c.tangent_mul_star s
      change c.tangent s * conj (c.tangent s) = 1 at h
      rw [h]; ring

theorem tangent_from_invertedStress (s : ℝ) (hs : c.stress s ≠ 0) :
    c.tangent s = ((c.curvature s : ℂ)^2 / 2) * c.invertedStress s -
      (c.curvature₁ s : ℂ) * (Complex.I * c.invertedStress s) := by
  have hstar : star (c.stress s) ≠ 0 := star_ne_zero.mpr hs
  have h := c.tangent_mul_star_stress s
  dsimp [invertedStress]
  calc
    _ = (c.tangent s * star (c.stress s)) * (star (c.stress s))⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hstar, mul_one]
    _ = _ := by rw [h]; simp only [Complex.star_def]; ring

theorem invertedStress_deriv (s : ℝ) (hs : c.stress s ≠ 0) :
    HasDerivAt c.invertedStress (c.invertedStressDerivative s) s := by
  exact (c.stress_deriv s).star.inv (star_ne_zero.mpr hs)

theorem invertedStressDerivative_norm (s : ℝ) :
    ‖c.invertedStressDerivative s‖ = |c.force s| / ‖c.stress s‖^2 := by
  simp [invertedStressDerivative, norm_pow, c.normal_unit]

theorem stress_periodic : Function.Periodic c.stress c.period := by
  intro s
  simp only [stress, normal, c.curvature_periodic s, c.curvature₁_periodic s,
    c.tangent_periodic s]

theorem invertedStress_periodic : Function.Periodic c.invertedStress c.period := by
  intro s
  simp only [invertedStress, c.stress_periodic s]

theorem invertedStress_continuous (hW : ∀ s, c.stress s ≠ 0) :
    Continuous c.invertedStress :=
  continuous_iff_continuousAt.mpr fun s =>
    (c.invertedStress_deriv s (hW s)).continuousAt

theorem invertedStressDerivative_continuous (hW : ∀ s, c.stress s ≠ 0) :
    Continuous c.invertedStressDerivative := by
  have hN : Continuous c.normal := continuous_const.mul c.tangent_continuous
  exact (((Complex.continuous_ofReal.comp c.force_continuous).mul hN).star.neg).div
    (c.stress_continuous.star.pow 2)
    (fun s => pow_ne_zero 2 (star_ne_zero.mpr (hW s)))

/-- Closure and integration by parts produce the stress identity. The only
extra hypothesis here is nonvanishing of the actual stress, as required
to define its smooth inversion. Later estimates derive it in the small
dissipation contradiction argument. -/
theorem closed_stress_integral (hW : ∀ s, c.stress s ≠ 0) :
    (∫ s in 0..c.period,
      ((c.curvature s : ℂ)^2 / 2) * c.invertedStress s) =
    -(∫ s in 0..c.period,
      (c.curvature s : ℂ) * (Complex.I * c.invertedStressDerivative s)) := by
  let a : ℝ → ℂ := fun s =>
    ((c.curvature s : ℂ)^2 / 2) * c.invertedStress s
  let b : ℝ → ℂ := fun s =>
    (c.curvature₁ s : ℂ) * (Complex.I * c.invertedStress s)
  let d : ℝ → ℂ := fun s =>
    (c.curvature s : ℂ) * (Complex.I * c.invertedStressDerivative s)
  have hcV := c.invertedStress_continuous hW
  have hcd := c.invertedStressDerivative_continuous hW
  have ha : Continuous a :=
    (((Complex.continuous_ofReal.comp c.curvature_continuous).pow 2).div_const 2).mul hcV
  have hb : Continuous b :=
    (Complex.continuous_ofReal.comp c.curvature₁_continuous).mul (continuous_const.mul hcV)
  have hd : Continuous d :=
    (Complex.continuous_ofReal.comp c.curvature_continuous).mul (continuous_const.mul hcd)
  have hder : ∀ s, HasDerivAt
      (fun u => (c.curvature u : ℂ) * (Complex.I * c.invertedStress u))
      (b s + d s) s := by
    intro s
    exact (c.curvature_deriv s).ofReal_comp.mul
      ((c.invertedStress_deriv s (hW s)).const_mul Complex.I)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hder s) ((hb.add hd).intervalIntegrable 0 c.period)
  have hk : c.curvature c.period = c.curvature 0 := by
    simpa using c.curvature_periodic 0
  have hv : c.invertedStress c.period = c.invertedStress 0 := by
    simpa using c.invertedStress_periodic 0
  rw [hk, hv, sub_self, intervalIntegral.integral_add
    (hb.intervalIntegrable _ _) (hd.intervalIntegrable _ _)] at hi
  have ht : c.tangent = fun s => a s - b s := by
    funext s
    exact c.tangent_from_invertedStress s (hW s)
  have htint := c.tangent_integral_zero
  rw [ht, intervalIntegral.integral_sub
    (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _)] at htint
  change (∫ s in 0..c.period, a s) = -(∫ s in 0..c.period, d s)
  exact (sub_eq_zero.mp htint).trans (eq_neg_iff_add_eq_zero.mpr hi)

end ClosedFrenetCurve
end LengthGrowth

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"LengthGrowth elastic-stress audit passed for {checked} declarations."
