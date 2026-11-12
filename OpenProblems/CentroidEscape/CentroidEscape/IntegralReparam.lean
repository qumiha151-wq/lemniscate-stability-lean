import CentroidEscape.ParameterFlow
import CentroidEscape.Centroid
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace CentroidEscape
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

/-- Change of variables for a Lipschitz lift. Spatial C1 regularity is not
assumed: the proof uses actual a.e. differentiability and the absolutely
continuous fundamental theorem of calculus. -/
theorem integral_substitution_lipschitz {f φ : ℝ → ℝ} {M K : ℝ≥0}
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ M) (hφ : LipschitzWith K φ) (a b : ℝ) :
    (∫ s in a..b, f (φ s) * deriv φ s) = ∫ u in φ a..φ b, f u := by
  let F : ℝ → ℝ := fun x => ∫ u in 0..x, f u
  have hFd : ∀ x, HasDerivAt F (f x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter (hf.continuousAt)
  have hFLip : LipschitzWith M F := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hFd x).differentiableAt)
    intro x
    rw [(hFd x).deriv]
    exact_mod_cast hb x
  have hAC : AbsolutelyContinuousOnInterval (fun x => F (φ x)) a b :=
    (hFLip.comp hφ).lipschitzOnWith.absolutelyContinuousOnInterval
  have hd : ∀ᵐ x, deriv (fun s => F (φ s)) x = f (φ x) * deriv φ x := by
    filter_upwards [hφ.ae_differentiableAt_real] with x hx
    convert! ((hFd (φ x)).comp x hx.hasDerivAt).deriv using 1
  calc
    (∫ s in a..b, f (φ s) * deriv φ s) = ∫ s in a..b, deriv (fun u => F (φ u)) s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with x hx _
      exact hx.symm
    _ = F (φ b) - F (φ a) := hAC.integral_deriv_eq_sub
    _ = ∫ u in φ a..φ b, f u :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hFd x)
        (hf.intervalIntegrable _ _)).symm

theorem parameterFlow_periodic_integral (G : ParameterFieldData) {P : ℝ}
    (hgp : Function.Periodic G.field P) {f : ℝ → ℝ} (hf : Continuous f)
    (hfp : Function.Periodic f P) (hP : P ≠ 0) (t : ℝ) :
    (∫ s in 0..P, f (parameterFlow G t s) * deriv (parameterFlow G t) s) =
      ∫ s in 0..P, f s := by
  obtain ⟨M, hM⟩ := periodic_continuous_norm_bound hfp hP hf
  rw [integral_substitution_lipschitz hf hM (parameterFlow_lipschitz G t)]
  rw [show parameterFlow G t P = parameterFlow G t 0 + P by
    simpa using parameterFlow_period_lift G hgp t 0]
  simpa only [zero_add] using hfp.intervalIntegral_add_eq (parameterFlow G t 0) 0

lemma reparametrized_expandingCurve_speed_ae {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1) (G : ParameterFieldData) (τ : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ s, ‖deriv (fun r => expandingCurve q t (parameterFlow G τ r)) s‖ =
      expanderRadius t * deriv (parameterFlow G τ) s := by
  filter_upwards [(parameterFlow_lipschitz G τ).ae_differentiableAt_real] with s hs
  have hd := (expandingCurve_space_derivative hq t (parameterFlow G τ s)).scomp s hs.hasDerivAt
  have hd' : HasDerivAt (fun r => expandingCurve q t (parameterFlow G τ r))
      (deriv (parameterFlow G τ) s • (expanderRadius t • tangent (q (parameterFlow G τ s)))) s := by
    convert! hd using 1
  have hnonneg : 0 ≤ deriv (parameterFlow G τ) s :=
    (parameterFlow_strictMono G τ).monotone.deriv_nonneg
  rw [hd'.deriv, norm_smul, norm_smul, tangent_norm_one (hu _),
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_pos (expanderRadius_pos ht)]
  ring

/-- The actual arclength centroid, using the norm of the derivative of the
reparametrized curve, is invariant. No spatial differentiability of the lift
is assumed; Lipschitz absolute continuity and a.e. chain rule supply it. -/
theorem reparametrized_expandingCurve_centroid {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1) (hp : Function.Periodic q P) (hP : P ≠ 0)
    (G : ParameterFieldData) (hgp : Function.Periodic G.field P) (τ : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    curveCentroidX P (fun s => expandingCurve q t (parameterFlow G τ s)) =
      curveCentroidX P (expandingCurve q t) := by
  have hs := reparametrized_expandingCurve_speed_ae hq hu G τ ht
  have hqc : Continuous (fun s => q s 0) := continuous_iff_continuousAt.mpr
    fun s => (hasDerivAt_pi.mp (hq s) 0).continuousAt
  have hqp : Function.Periodic (fun s => q s 0) P := fun s => congrFun (hp s) 0
  have hx := parameterFlow_periodic_integral G hgp hqc hqp hP τ
  have hi : (∫ s in 0..P, deriv (parameterFlow G τ) s) = P := by
    have hh := parameterFlow_periodic_integral G hgp continuous_const
      (show Function.Periodic (fun _ : ℝ => (1:ℝ)) P from fun _ => rfl) hP τ
    simpa using hh
  have hden : (∫ s in 0..P,
      ‖deriv (fun r => expandingCurve q t (parameterFlow G τ r)) s‖) = expanderRadius t * P := by
    calc
      _ = ∫ s in 0..P, expanderRadius t * deriv (parameterFlow G τ) s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hs] with s hss _
        exact hss
      _ = _ := by rw [intervalIntegral.integral_const_mul, hi]
  have hnum : (∫ s in 0..P,
      expandingCurve q t (parameterFlow G τ s) 0 *
        ‖deriv (fun r => expandingCurve q t (parameterFlow G τ r)) s‖) =
      expanderRadius t ^ 2 * (∫ s in 0..P, q s 0) := by
    calc
      _ = ∫ s in 0..P, expanderRadius t ^ 2 *
          (q (parameterFlow G τ s) 0 * deriv (parameterFlow G τ) s) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hs] with s hss _
        rw [hss]
        simp [expandingCurve, position, planePair]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul, hx]
  rw [curveCentroidX, arclengthMean, hnum, hden,
    expandingCurve_centroid_x hq hu ht]
  field_simp [(expanderRadius_pos ht).ne', hP]

def coherentExpandingCurve {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (t s : ℝ) : Plane :=
  expandingCurve q t (profileParameterLift hq hp hP t s)

theorem coherentExpandingCurve_centroid {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1) (hp : Function.Periodic q P) (hP : P ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    curveCentroidX P (coherentExpandingCurve hq hp hP t) =
      curveCentroidX P (expandingCurve q t) :=
  reparametrized_expandingCurve_centroid hq hu hp hP (profileParameterData hq hp hP)
    (profileParameterData_periodic hq hp hP) (logarithmicTime t) ht

theorem coherentExpandingCurve_centroid_escapes {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1) (hp : Function.Periodic q P) (hP : P ≠ 0)
    (hmean : 0 < (∫ s in 0..P, q s 0) / P) :
    Tendsto (fun t => curveCentroidX P (coherentExpandingCurve hq hp hP t)) atTop atTop := by
  apply (expandingCurve_centroid_escapes hq hu hmean).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact (coherentExpandingCurve_centroid hq hu hp hP ht).symm

end
end CentroidEscape

#print axioms CentroidEscape.reparametrized_expandingCurve_centroid
#print axioms CentroidEscape.coherentExpandingCurve_centroid_escapes

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Centroid integral-reparametrization audit passed for {checked} declarations."
