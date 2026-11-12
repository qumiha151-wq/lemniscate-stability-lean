import OpenTranslators.BoundedFlow
import OpenTranslators.RegularizedField
import OpenTranslators.Bounds
import OpenTranslators.LocalUniqueness
import OpenTranslators.SmoothFlow
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.MonotoneContinuity

/-! Construction of the original global translator flow by proving that the
actual regularized-flow clock is an order isomorphism of the real line. -/

namespace OpenTranslator
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- A positive clock cannot have a finite upper bound when its denominator is
controlled by a positive radius whose rate is at most the clock's rate. -/
theorem clock_not_bddAbove {S R D r : ℝ → ℝ}
    (hS0 : S 0 = 0) (hRpos : ∀ t, 0 < R t) (hDpos : ∀ t, 0 < D t)
    (hS : ∀ t, HasDerivAt S (1 / D t) t)
    (hR : ∀ t, HasDerivAt R (r t) t)
    (hr : ∀ t, |r t| ≤ 1 / D t)
    (hDR : ∀ t, D t ≤ 2 * R t ^ 2) : ¬ BddAbove (range S) := by
  rintro ⟨K, hK⟩
  have hK0 : 0 ≤ K := by simpa only [hS0] using hK (mem_range_self 0)
  have hdiff : Differentiable ℝ S := fun t => (hS t).differentiableAt
  have hmono : Monotone (fun t => S t - R t) :=
    monotone_of_hasDerivAt_nonneg (fun t => (hS t).sub (hR t))
      (fun t => sub_nonneg.mpr ((le_abs_self (r t)).trans (hr t)))
  have hRbound (t : ℝ) (ht : 0 ≤ t) : R t ≤ R 0 + K := by
    have h := hmono ht
    change S 0 - R 0 ≤ S t - R t at h
    have hKt := hK (mem_range_self t)
    rw [hS0] at h
    linarith
  let E : ℝ := 2 * (R 0 + K) ^ 2
  have hE : 0 < E := by
    have hR0 := hRpos 0
    dsimp [E]
    positivity
  have hDbound (t : ℝ) (ht : 0 ≤ t) : D t ≤ E := by
    have h := hRbound t ht
    have hp := hRpos t
    have hd := hDR t
    dsimp [E]
    nlinarith
  have hderiv : ∀ t ∈ interior (Ici (0:ℝ)), 1 / E ≤ deriv S t := by
    intro t ht
    rw [(hS t).deriv]
    exact one_div_le_one_div_of_le (hDpos t) (hDbound t (interior_subset ht))
  let T : ℝ := E * (K + 1)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hgrowth := (convex_Ici (0:ℝ)).mul_sub_le_image_sub_of_le_deriv
    hdiff.continuous.continuousOn hdiff.differentiableOn hderiv 0 (by simp) T hT hT
  have heval : 1 / E * (T - 0) = K + 1 := by
    dsimp [T]
    field_simp
    ring
  rw [heval, hS0, sub_zero] at hgrowth
  have hKT := hK (mem_range_self T)
  linarith

/-- The same argument in reverse time rules out a finite lower endpoint. -/
theorem clock_not_bddBelow {S R D r : ℝ → ℝ}
    (hS0 : S 0 = 0) (hRpos : ∀ t, 0 < R t) (hDpos : ∀ t, 0 < D t)
    (hS : ∀ t, HasDerivAt S (1 / D t) t)
    (hR : ∀ t, HasDerivAt R (r t) t)
    (hr : ∀ t, |r t| ≤ 1 / D t)
    (hDR : ∀ t, D t ≤ 2 * R t ^ 2) : ¬ BddBelow (range S) := by
  have hrev := clock_not_bddAbove
    (S := fun t => -S (-t)) (R := fun t => R (-t))
    (D := fun t => D (-t)) (r := fun t => -r (-t))
    (by simp [hS0]) (fun t => hRpos (-t)) (fun t => hDpos (-t))
    (fun t => by
      convert ((hS (-t)).comp t (hasDerivAt_id t).neg).neg using 1 <;>
        first | rfl | simp)
    (fun t => by simpa [Function.comp_def] using (hR (-t)).comp t (hasDerivAt_id t).neg)
    (fun t => by simpa only [abs_neg] using hr (-t)) (fun t => hDR (-t))
  rintro ⟨K, hK⟩
  apply hrev
  refine ⟨-K, ?_⟩
  rintro y ⟨t, rfl⟩
  exact neg_le_neg (hK (mem_range_self (-t)))

theorem clock_surjective {S R D r : ℝ → ℝ}
    (hS0 : S 0 = 0) (hRpos : ∀ t, 0 < R t) (hDpos : ∀ t, 0 < D t)
    (hS : ∀ t, HasDerivAt S (1 / D t) t)
    (hR : ∀ t, HasDerivAt R (r t) t)
    (hr : ∀ t, |r t| ≤ 1 / D t)
    (hDR : ∀ t, D t ≤ 2 * R t ^ 2) : Function.Surjective S := by
  apply range_eq_univ.mp
  exact (isPreconnected_range (continuous_iff_continuousAt.mpr
    (fun t => (hS t).continuousAt))).eq_univ_of_unbounded
    (clock_not_bddBelow hS0 hRpos hDpos hS hR hr hDR)
    (clock_not_bddAbove hS0 hRpos hDpos hS hR hr hDR)

def regularizedClock (z : ℝ → TranslatorState) (t : ℝ) : ℝ :=
  ∫ u in 0..t, 1 / regularizingDenominator (z u)

def regularizedRadius (z : ℝ → TranslatorState) (t : ℝ) : ℝ :=
  energyRadius (z t 1) (z t 2)

def regularizedRadiusRate (z : ℝ → TranslatorState) (t : ℝ) : ℝ :=
  (z t 2 * Real.sin (z t 0) / (2 * regularizedRadius z t)) /
    regularizingDenominator (z t)

theorem regularizedFlow_continuous {z : ℝ → TranslatorState}
    (hz : ∀ t, HasDerivAt z (regularizedField (z t)) t) : Continuous z :=
  continuous_iff_continuousAt.mpr (fun t => (hz t).continuousAt)

theorem regularizedClock_hasDerivAt {z : ℝ → TranslatorState}
    (hz : ∀ t, HasDerivAt z (regularizedField (z t)) t) (t : ℝ) :
    HasDerivAt (regularizedClock z) (1 / regularizingDenominator (z t)) t := by
  have hc : Continuous (fun u => 1 / regularizingDenominator (z u)) :=
    continuous_const.div (regularizingDenominator_smooth.continuous.comp
      (regularizedFlow_continuous hz)) (fun u => regularizingDenominator_ne_zero (z u))
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

@[simp] theorem regularizedClock_zero (z : ℝ → TranslatorState) : regularizedClock z 0 = 0 := by
  simp [regularizedClock]

theorem regularizedRadius_pos (z : ℝ → TranslatorState) (t : ℝ) :
    0 < regularizedRadius z t := energyRadius_pos _ _

theorem regularizedEnergy_hasDerivAt {z : ℝ → TranslatorState}
    (hz : ∀ t, HasDerivAt z (regularizedField (z t)) t) (t : ℝ) :
    HasDerivAt (fun u => quarticEnergy (z u 1) (z u 2))
      (z t 2 * Real.sin (z t 0) / regularizingDenominator (z t)) t := by
  have hk := hasDerivAt_pi.mp (hz t) 1
  have hv := hasDerivAt_pi.mp (hz t) 2
  change HasDerivAt (fun u => z u 1)
    (z t 2 / regularizingDenominator (z t)) t at hk
  change HasDerivAt (fun u => z u 2)
    ((-(z t 1)^3/2 + Real.sin (z t 0)) / regularizingDenominator (z t)) t at hv
  convert ((hv.pow 2).div_const 2).add ((hk.pow 4).div_const 8) using 1 <;>
    first | rfl | (field_simp; ring)

theorem regularizedRadius_hasDerivAt {z : ℝ → TranslatorState}
    (hz : ∀ t, HasDerivAt z (regularizedField (z t)) t) (t : ℝ) :
    HasDerivAt (regularizedRadius z) (regularizedRadiusRate z t) t := by
  have hpos : quarticEnergy (z t 1) (z t 2) + 1 ≠ 0 := by
    linarith [quarticEnergy_nonneg (z t 1) (z t 2)]
  convert ((regularizedEnergy_hasDerivAt hz t).add_const 1).sqrt hpos using 1 <;>
    first | rfl | (dsimp [regularizedRadiusRate, regularizedRadius, energyRadius]; ring)

theorem regularizedRadiusRate_abs_le (z : ℝ → TranslatorState) (t : ℝ) :
    |regularizedRadiusRate z t| ≤ 1 / regularizingDenominator (z t) := by
  rw [regularizedRadiusRate, abs_div, abs_of_pos (regularizingDenominator_pos (z t))]
  apply div_le_div_of_nonneg_right _ (regularizingDenominator_pos (z t)).le
  exact energyRadius_derivative_norm_le_one (z t 0) (z t 1) (z t 2)

theorem denominator_le_twice_radius_sq (z : ℝ → TranslatorState) (t : ℝ) :
    regularizingDenominator (z t) ≤ 2 * regularizedRadius z t ^ 2 := by
  have hR := energyRadius_sq (z t 1) (z t 2)
  dsimp [regularizingDenominator, regularizedRadius, quarticEnergy] at *
  linarith

theorem regularizedClock_strictMono {z : ℝ → TranslatorState}
    (hz : ∀ t, HasDerivAt z (regularizedField (z t)) t) : StrictMono (regularizedClock z) :=
  strictMono_of_hasDerivAt_pos (regularizedClock_hasDerivAt hz)
    (fun t => one_div_pos.mpr (regularizingDenominator_pos (z t)))

/-- The clock is onto by the proved energy-radius argument, not an assumption. -/
theorem regularizedClock_surjective {z : ℝ → TranslatorState}
    (hz : ∀ t, HasDerivAt z (regularizedField (z t)) t) :
    Function.Surjective (regularizedClock z) :=
  clock_surjective (regularizedClock_zero z) (regularizedRadius_pos z)
    (fun t => regularizingDenominator_pos (z t)) (regularizedClock_hasDerivAt hz)
    (regularizedRadius_hasDerivAt hz) (regularizedRadiusRate_abs_le z)
    (denominator_le_twice_radius_sq z)

def regularizedClockOrderIso {z : ℝ → TranslatorState}
    (hz : ∀ t, HasDerivAt z (regularizedField (z t)) t) : ℝ ≃o ℝ :=
  (regularizedClock_strictMono hz).orderIsoOfSurjective (regularizedClock z)
    (regularizedClock_surjective hz)

theorem inverseClock_hasDerivAt {z : ℝ → TranslatorState}
    (hz : ∀ t, HasDerivAt z (regularizedField (z t)) t) (t : ℝ) :
    HasDerivAt (regularizedClockOrderIso hz).symm
      (regularizingDenominator (z ((regularizedClockOrderIso hz).symm t))) t := by
  let e := regularizedClockOrderIso hz
  have hh := HasDerivAt.of_local_left_inverse e.symm.toHomeomorph.continuous.continuousAt
    (regularizedClock_hasDerivAt hz (e.symm t))
    (one_div_ne_zero (regularizingDenominator_ne_zero _))
    (Filter.Eventually.of_forall (fun s => e.apply_symm_apply s))
  convert hh using 1 <;> first | rfl | (simp only [one_div, inv_inv]; rfl)

/-- Pulling the actual global regularized flow back by its inverse clock gives
an actual global solution of the original cubic translator field. -/
theorem reparametrizedFlow_hasDerivAt {z : ℝ → TranslatorState}
    (hz : ∀ t, HasDerivAt z (regularizedField (z t)) t) (t : ℝ) :
    HasDerivAt (fun s => z ((regularizedClockOrderIso hz).symm s))
      (translatorNumerator (z ((regularizedClockOrderIso hz).symm t))) t := by
  have hh := (hz ((regularizedClockOrderIso hz).symm t)).scomp t (inverseClock_hasDerivAt hz t)
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, regularizedField]
  field_simp [regularizingDenominator_ne_zero]

/-- Every initial state of the original translator ODE has a global solution. -/
theorem exists_global_translator (z₀ : TranslatorState) :
    ∃ x : ℝ → TranslatorState, x 0 = z₀ ∧ ∀ t, HasDerivAt x (translatorNumerator (x t)) t := by
  obtain ⟨z, hz, _⟩ := exists_unique_global_bounded_flow
    regularizedField_lipschitz (M := 3) regularizedField_norm_le z₀
  let e := regularizedClockOrderIso hz.2
  have he0 : e 0 = 0 := regularizedClock_zero z
  have hinv0 : e.symm 0 = 0 := by simpa only [he0] using e.symm_apply_apply 0
  refine ⟨fun s => z (e.symm s), ?_, reparametrizedFlow_hasDerivAt hz.2⟩
  simpa only [hinv0] using hz.1

/-- The constructed global translator is unique among all actual global
solutions, using the proved smoothness of the original polynomial/trigonometric field. -/
theorem exists_unique_global_translator (z₀ : TranslatorState) :
    ∃! x : ℝ → TranslatorState, x 0 = z₀ ∧ ∀ t, HasDerivAt x (translatorNumerator (x t)) t := by
  obtain ⟨x, hx0, hx⟩ := exists_global_translator z₀
  refine ⟨x, ⟨hx0, hx⟩, ?_⟩
  intro y hy
  have hC1 : ContDiff ℝ 1 translatorNumerator := translatorNumerator_smooth.of_le (by simp)
  exact unique_global_of_locallyLipschitz hC1.locallyLipschitz hy.2 hx (hy.1.trans hx0.symm)

/-- Actual global solutions are smooth as a consequence of the smooth field. -/
theorem global_translator_smooth {x : ℝ → TranslatorState}
    (hx : ∀ t, HasDerivAt x (translatorNumerator (x t)) t) : ContDiff ℝ ∞ x :=
  smooth_integral_curve_of_smooth_field translatorNumerator_smooth hx

theorem exists_unique_smooth_global_translator (z₀ : TranslatorState) :
    ∃! x : ℝ → TranslatorState, x 0 = z₀ ∧ ContDiff ℝ ∞ x ∧
      ∀ t, HasDerivAt x (translatorNumerator (x t)) t := by
  obtain ⟨x, hx, huniq⟩ := exists_unique_global_translator z₀
  exact ⟨x, ⟨hx.1, global_translator_smooth hx.2, hx.2⟩,
    fun y hy => huniq y ⟨hy.1, hy.2.2⟩⟩

end
end OpenTranslator

#print axioms OpenTranslator.exists_unique_global_translator

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"RegularizedGlobal: audited {checked} declarations; standard axioms only."
