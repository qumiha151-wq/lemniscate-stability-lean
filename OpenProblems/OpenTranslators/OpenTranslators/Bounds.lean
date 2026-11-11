import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Positivity
import Lean.Util.CollectAxioms

/-!
# A priori bounds for the open free-elastic translator ODE

This module derives finite-interval bounds directly from the differential
equations k' = v and v' = -k^3/2 + sin(theta). It does not assume an energy
inequality. It does not yet formalize local existence, continuation, or the
geometric reconstruction of a complete translator.
-/

namespace OpenTranslator

noncomputable section

def quarticEnergy (k v : ℝ) : ℝ := v^2/2 + k^4/8

def energyRadius (k v : ℝ) : ℝ := Real.sqrt (quarticEnergy k v + 1)

lemma quarticEnergy_nonneg (k v : ℝ) : 0 ≤ quarticEnergy k v := by
  unfold quarticEnergy
  positivity

lemma energyRadius_pos (k v : ℝ) : 0 < energyRadius k v := by
  apply Real.sqrt_pos.2
  linarith [quarticEnergy_nonneg k v]

lemma energyRadius_sq (k v : ℝ) : (energyRadius k v)^2 = quarticEnergy k v + 1 := by
  exact Real.sq_sqrt (by linarith [quarticEnergy_nonneg k v])

lemma velocity_bound (k v : ℝ) : |v| ≤ 2 * energyRadius k v := by
  have h0 := energyRadius_pos k v
  have h1 := energyRadius_sq k v
  have h2 : v^2 ≤ 2*quarticEnergy k v := by
    unfold quarticEnergy
    nlinarith [sq_nonneg (k^2)]
  nlinarith [sq_abs v, abs_nonneg v, quarticEnergy_nonneg k v]

lemma curvature_bound (k v : ℝ) : |k| ≤ 4 * energyRadius k v := by
  have h0 := energyRadius_pos k v
  have h1 := energyRadius_sq k v
  have h2 : k^4 ≤ 8*quarticEnergy k v := by
    unfold quarticEnergy
    nlinarith [sq_nonneg v]
  have h3 : k^2 ≤ k^4 + 1 := by
    nlinarith [sq_nonneg (k^2-1), sq_nonneg k]
  nlinarith [sq_abs k, abs_nonneg k, quarticEnergy_nonneg k v]

theorem quarticEnergy_hasDerivAt (theta k v : ℝ → ℝ) (x : ℝ)
    (hk : HasDerivAt k (v x) x)
    (hv : HasDerivAt v (-(k x)^3/2 + Real.sin (theta x)) x) :
    HasDerivAt (fun s => quarticEnergy (k s) (v s))
      (v x * Real.sin (theta x)) x := by
  unfold quarticEnergy
  convert! ((hv.pow 2).div_const 2).add ((hk.pow 4).div_const 8) using 1
  ring

theorem energyRadius_hasDerivAt (theta k v : ℝ → ℝ) (x : ℝ)
    (hk : HasDerivAt k (v x) x)
    (hv : HasDerivAt v (-(k x)^3/2 + Real.sin (theta x)) x) :
    HasDerivAt (fun s => energyRadius (k s) (v s))
      (v x * Real.sin (theta x) / (2 * energyRadius (k x) (v x))) x := by
  exact ((quarticEnergy_hasDerivAt theta k v x hk hv).add_const 1).sqrt
    (by linarith [quarticEnergy_nonneg (k x) (v x)])

lemma energyRadius_derivative_norm_le_one (theta k v : ℝ) :
    ‖v * Real.sin theta / (2 * energyRadius k v)‖ ≤ 1 := by
  have hden : 0 < 2 * energyRadius k v := by
    linarith [energyRadius_pos k v]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |v * Real.sin theta| = |v| * |Real.sin theta| := abs_mul _ _
    _ ≤ |v| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one theta) (abs_nonneg _)
    _ ≤ 1 * (2 * energyRadius k v) := by simpa using velocity_bound k v

/-- The energy radius is 1-Lipschitz on every convex portion of an actual
solution. This gives a polynomial energy bound on any finite interval. -/
theorem energyRadius_lipschitzOn_solution (theta k v : ℝ → ℝ) (D : Set ℝ)
    (hD : Convex ℝ D)
    (hk : ∀ x ∈ D, HasDerivAt k (v x) x)
    (hv : ∀ x ∈ D, HasDerivAt v (-(k x)^3/2 + Real.sin (theta x)) x)
    (a b : ℝ) (ha : a ∈ D) (hb : b ∈ D) :
    |energyRadius (k b) (v b) - energyRadius (k a) (v a)| ≤ |b-a| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (energyRadius_hasDerivAt theta k v x (hk x hx) (hv x hx)).hasDerivWithinAt)
    (fun x _ => energyRadius_derivative_norm_le_one (theta x) (k x) (v x)) hD ha hb
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem quarticEnergy_bound_on_solution (theta k v : ℝ → ℝ) (D : Set ℝ)
    (hD : Convex ℝ D)
    (hk : ∀ x ∈ D, HasDerivAt k (v x) x)
    (hv : ∀ x ∈ D, HasDerivAt v (-(k x)^3/2 + Real.sin (theta x)) x)
    (a b : ℝ) (ha : a ∈ D) (hb : b ∈ D) :
    quarticEnergy (k b) (v b) + 1 ≤
      (energyRadius (k a) (v a) + |b-a|)^2 := by
  have h := energyRadius_lipschitzOn_solution theta k v D hD hk hv a b ha hb
  have hr : energyRadius (k b) (v b) ≤ energyRadius (k a) (v a) + |b-a| := by
    linarith [(abs_le.1 h).2]
  rw [← energyRadius_sq]
  exact pow_le_pow_left₀ (le_of_lt (energyRadius_pos _ _)) hr 2

/-- An actual translator ODE trajectory stays in an explicit bounded box
on a bounded convex time domain. No boundedness hypothesis on the solution
is imposed; the bound is derived from its equations and initial data.
This is the non-escape estimate needed for a future formal continuation
argument. Local existence and continuation are not claimed by this theorem. -/
theorem state_bounds_on_bounded_interval
    (theta k v : ℝ → ℝ) (D : Set ℝ) (hD : Convex ℝ D)
    (hth : ∀ x ∈ D, HasDerivAt theta (k x) x)
    (hk : ∀ x ∈ D, HasDerivAt k (v x) x)
    (hv : ∀ x ∈ D, HasDerivAt v (-(k x)^3/2 + Real.sin (theta x)) x)
    (a R : ℝ) (ha : a ∈ D) (hR : 0 ≤ R)
    (hbounded : ∀ x ∈ D, |x-a| ≤ R) :
    ∀ b ∈ D,
      |v b| ≤ 2 * (energyRadius (k a) (v a) + R) ∧
      |k b| ≤ 4 * (energyRadius (k a) (v a) + R) ∧
      |theta b-theta a| ≤ 4 * (energyRadius (k a) (v a) + R) * R := by
  have hr : ∀ x ∈ D, energyRadius (k x) (v x) ≤ energyRadius (k a) (v a) + R := by
    intro x hx
    have hb := energyRadius_lipschitzOn_solution theta k v D hD hk hv a x ha hx
    have hc := hbounded x hx
    linarith [(abs_le.1 hb).2]
  have hkb : ∀ x ∈ D, |k x| ≤ 4 * (energyRadius (k a) (v a) + R) := by
    intro x hx
    have hb := curvature_bound (k x) (v x)
    have hc := hr x hx
    linarith
  intro b hb
  refine ⟨?_, hkb b hb, ?_⟩
  · have h1 := velocity_bound (k b) (v b)
    have h2 := hr b hb
    linarith
  · have htheta := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hth x hx).hasDerivWithinAt)
      (fun x hx => (show ‖k x‖ ≤ 4 * (energyRadius (k a) (v a) + R) by
        simpa only [Real.norm_eq_abs] using hkb x hx)) hD ha hb
    have hnonneg : 0 ≤ 4 * (energyRadius (k a) (v a) + R) := by
      linarith [energyRadius_pos (k a) (v a)]
    have hstep := mul_le_mul_of_nonneg_left (hbounded b hb) hnonneg
    have htheta' : |theta b-theta a| ≤
        4 * (energyRadius (k a) (v a) + R) * |b-a| := by
      simpa only [Real.norm_eq_abs] using htheta
    exact htheta'.trans hstep

#print axioms quarticEnergy_hasDerivAt
#print axioms energyRadius_lipschitzOn_solution
#print axioms quarticEnergy_bound_on_solution
#print axioms state_bounds_on_bounded_interval

end
end OpenTranslator

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  unless checked > 0 do
    throwError "No translator declarations were checked"
  logInfo m!"Translator estimate audit passed for {checked} declarations."
