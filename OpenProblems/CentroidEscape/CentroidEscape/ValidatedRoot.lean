import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Util.CollectAxioms

/-!
# Validated shooting: from analytic bounds to an exact zero

This module proves the fixed-point implication needed by the asymmetric
closed-expander certificate. It does not assume the existence of a zero.
The hypotheses about the shooting map, its derivative, and its residual
still have to be established from the ODE and the numerical certificate.
Those hypotheses are NOT claimed to be discharged in this module.
-/

namespace CentroidEscape
noncomputable section
open Set Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A residual and uniform preconditioned derivative bound give an actual
unique zero in a complete closed ball. Existence is a conclusion, not a
hypothesis. The ball may be an infinity-norm cube, as in the certificate. -/
theorem exists_unique_zero_of_preconditioned_bounds
    (F : E → E) (DF : E → E →L[ℝ] E) (B : E →L[ℝ] E)
    (p : E) (r η : ℝ) (q : ℝ≥0)
    (hr : 0 ≤ r) (hq : q < 1) (hB : Function.Injective B)
    (hF : ∀ x ∈ closedBall p r, HasFDerivAt F (DF x) x)
    (hD : ∀ x ∈ closedBall p r,
      ‖ContinuousLinearMap.id ℝ E - B.comp (DF x)‖ ≤ (q : ℝ))
    (hres : ‖B (F p)‖ ≤ η)
    (hself : η + (q : ℝ) * r ≤ r) :
    ∃ x ∈ closedBall p r, F x = 0 ∧
      ∀ y ∈ closedBall p r, F y = 0 → y = x := by
  let T : E → E := fun x => x - B (F x)
  have hp : p ∈ closedBall p r := mem_closedBall_self hr
  have hT : ∀ x ∈ closedBall p r,
      HasFDerivAt T (ContinuousLinearMap.id ℝ E - B.comp (DF x)) x := by
    intro x hx
    exact (hasFDerivAt_id x).sub (B.hasFDerivAt.comp x (hF x hx))
  have hLip : ∀ x ∈ closedBall p r, ∀ y ∈ closedBall p r,
      ‖T x - T y‖ ≤ (q : ℝ) * ‖x-y‖ := by
    intro x hx y hy
    exact (convex_closedBall p r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hT z hz).hasFDerivWithinAt) hD hy hx
  have hcenter : ‖T p - p‖ ≤ η := by
    simpa only [T, sub_sub_cancel_left, norm_neg] using hres
  have hmap : MapsTo T (closedBall p r) (closedBall p r) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖T x-p‖ ≤ ‖T x-T p‖ + ‖T p-p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (q : ℝ) * ‖x-p‖ + η := add_le_add (hLip x hx p hp) hcenter
      _ ≤ (q : ℝ) * r + η := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hx) q.coe_nonneg) le_rfl
      _ ≤ r := by linarith
  have hcontract : ContractingWith q (hmap.restrict T _ _) := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (T x) (T y) ≤ (q : ℝ) * dist (x : E) (y : E)
    simpa only [dist_eq_norm] using hLip x x.property y y.property
  obtain ⟨x, hx, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hcontract hp (edist_ne_top p (T p))
  have hroot : F x = 0 := by
    apply hB
    rw [map_zero]
    have h : x - B (F x) = x := hfix
    exact sub_eq_self.mp h
  refine ⟨x, hx, hroot, ?_⟩
  intro y hy hyroot
  have hdist := hLip y hy x hx
  simp only [T, hyroot, hroot, map_zero, sub_zero] at hdist
  have hq' : (q : ℝ) < 1 := hq
  have hz : ‖y-x‖ = 0 := by nlinarith [norm_nonneg (y-x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Exact rational margins used in the independent Arb certificate. This
small arithmetic fact does not validate the ODE computation itself. -/
theorem certificate_self_map_margin :
    (1 / (10 : ℝ)^90) + (1 / (10 : ℝ)^8) * (1 / (10 : ℝ)^80)
      < 1 / (10 : ℝ)^80 := by
  norm_num

/-- The certificate's coarser published budgets suffice for exact shooting
existence once the stated analytic bounds have been proved for its map. -/
theorem exists_zero_of_certificate_budgets
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (DF : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (B : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (p : Fin 3 → ℝ)
    (hB : Function.Injective B)
    (hF : ∀ x ∈ closedBall p (1 / (10 : ℝ)^80), HasFDerivAt F (DF x) x)
    (hD : ∀ x ∈ closedBall p (1 / (10 : ℝ)^80),
      ‖ContinuousLinearMap.id ℝ (Fin 3 → ℝ) - B.comp (DF x)‖ ≤ 1 / (10 : ℝ)^8)
    (hres : ‖B (F p)‖ ≤ 1 / (10 : ℝ)^90) :
    ∃ x ∈ closedBall p (1 / (10 : ℝ)^80), F x = 0 ∧
      ∀ y ∈ closedBall p (1 / (10 : ℝ)^80), F y = 0 → y = x := by
  apply exists_unique_zero_of_preconditioned_bounds F DF B p
    (1 / (10 : ℝ)^80) (1 / (10 : ℝ)^90) ⟨1 / (10 : ℝ)^8, by positivity⟩
    (by positivity) (by change (1 / (10 : ℝ)^8) < 1; norm_num) hB hF hD hres
  exact le_of_lt certificate_self_map_margin

end
end CentroidEscape

#print axioms CentroidEscape.exists_unique_zero_of_preconditioned_bounds
#print axioms CentroidEscape.exists_zero_of_certificate_budgets

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
  unless checked > 0 do throwError "No centroid declarations checked"
  logInfo m!"Centroid root audit passed for {checked} declarations."
