import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-! A time integration estimate for the mass of a half-plane cutoff.
The mass and its local first-variation bound are inputs. The dissipation
density in time need only be interval integrable. -/

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry

def cutoffPrimitive (A B z : ℝ) : ℝ := ∫ m in 0..z, (B+A*Real.sqrt m)⁻¹

private theorem cutoffDensity_cont {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B) :
    Continuous (fun m => (B+A*Real.sqrt m)⁻¹) :=
  (continuous_const.add (Real.continuous_sqrt.const_mul A)).inv₀
    (fun m => ne_of_gt (add_pos_of_pos_of_nonneg hB (mul_nonneg hA (Real.sqrt_nonneg m))))

theorem cutoffPrimitive_hasDerivAt {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (z : ℝ) :
    HasDerivAt (cutoffPrimitive A B) ((B+A*Real.sqrt z)⁻¹) z := by
  have hc := cutoffDensity_cont hA hB
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 z)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem cutoffPrimitive_lower {A B W m : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (hW : 0 ≤ W) (hm : W ≤ m) :
    W / (B+A*Real.sqrt W) ≤ cutoffPrimitive A B m := by
  have hc := cutoffDensity_cont hA hB
  calc
    W / (B+A*Real.sqrt W) = ∫ _v in 0..W, (B+A*Real.sqrt W)⁻¹ := by
      rw [intervalIntegral.integral_const]
      simp [div_eq_mul_inv]
    _ ≤ cutoffPrimitive A B W := by
      apply intervalIntegral.integral_mono_on hW intervalIntegrable_const (hc.intervalIntegrable _ _)
      intro v hv
      apply inv_anti₀ (add_pos_of_pos_of_nonneg hB (mul_nonneg hA (Real.sqrt_nonneg v)))
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv.2) hA)
    _ ≤ cutoffPrimitive A B m := by
      apply intervalIntegral.integral_mono_interval le_rfl hW hm _ (hc.intervalIntegrable _ _)
      exact Filter.Eventually.of_forall (fun v =>
        inv_nonneg.mpr (add_nonneg hB.le (mul_nonneg hA (Real.sqrt_nonneg v))))

/-- The localized density can be discontinuous, for instance when it uses
an indicator of a spatial half-plane. -/
theorem cutoffPrimitive_change_sq_le {A B T : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (hT : 0 < T) (M V D : ℝ → ℝ)
    (hM : ContinuousOn M (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (hdM : ∀ x ∈ Ioo 0 T, HasDerivAt M (V x) x)
    (hD : IntervalIntegrable D volume 0 T)
    (hbound : ∀ x ∈ Icc 0 T, (V x)^2 ≤ (B+A*Real.sqrt (M x))^2 * D x) :
    (cutoffPrimitive A B (M T)-cutoffPrimitive A B (M 0))^2 ≤ T * ∫ x in 0..T, D x := by
  let J := cutoffPrimitive A B
  let q := fun x => (B+A*Real.sqrt (M x))⁻¹ * V x
  have hJ : Continuous J := continuous_iff_continuousAt.mpr fun z =>
    (cutoffPrimitive_hasDerivAt hA hB z).continuousAt
  have hq : ContinuousOn q (Icc 0 T) := ((cutoffDensity_cont hA hB).comp_continuousOn hM).mul hV
  have hqint : IntervalIntegrable q volume 0 T := hq.intervalIntegrable_of_Icc hT.le
  have hft : (∫ x in 0..T, q x) = J (M T)-J (M 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le (hJ.comp_continuousOn hM)
      (fun x hx => (cutoffPrimitive_hasDerivAt hA hB (M x)).comp x (hdM x hx)) hqint
  let a := (J (M T)-J (M 0))/T
  have hpt : ∀ x ∈ Icc 0 T, (2*a)*q x-a^2 ≤ D x := by
    intro x hx
    have hden := add_pos_of_pos_of_nonneg hB (mul_nonneg hA (Real.sqrt_nonneg (M x)))
    have hmul := mul_le_mul_of_nonneg_left (hbound x hx) (sq_nonneg ((B+A*Real.sqrt (M x))⁻¹))
    have hsq : (q x)^2 ≤ D x := by
      dsimp [q]
      rw [mul_pow]
      calc
        _ ≤ _ := hmul
        _ = D x := by
          rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hden), one_pow, one_mul]
    nlinarith [sq_nonneg (q x-a)]
  have h := intervalIntegral.integral_mono_on hT.le
    (((hq.const_mul (2*a)).sub continuousOn_const).intervalIntegrable_of_Icc hT.le) hD hpt
  change (∫ x in 0..T, (2*a)*q x-a^2) ≤ ∫ x in 0..T, D x at h
  rw [intervalIntegral.integral_sub (hqint.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hft, intervalIntegral.integral_const] at h
  simp only [sub_zero, smul_eq_mul] at h
  have ha : a*T = J (M T)-J (M 0) := div_mul_cancel₀ _ (ne_of_gt hT)
  change (J (M T)-J (M 0))^2 ≤ _
  calc
    _ = T*((2*a)*(J (M T)-J (M 0))-T*a^2) := by rw [← ha]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hT.le

/-- A mass changing between zero and at least W in either direction has a
positive localized cost. -/
theorem cutoffMass_transit_cost {A B W T : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (hW : 0 ≤ W) (hT : 0 < T) (M V D : ℝ → ℝ)
    (hM : ContinuousOn M (Icc 0 T)) (hV : ContinuousOn V (Icc 0 T))
    (hdM : ∀ x ∈ Ioo 0 T, HasDerivAt M (V x) x)
    (hD : IntervalIntegrable D volume 0 T)
    (hbound : ∀ x ∈ Icc 0 T, (V x)^2 ≤ (B+A*Real.sqrt (M x))^2 * D x)
    (hend : (W ≤ M 0 ∧ M T = 0) ∨ (M 0 = 0 ∧ W ≤ M T)) :
    (W / (B+A*Real.sqrt W))^2 ≤ T * ∫ x in 0..T, D x := by
  have h := cutoffPrimitive_change_sq_le hA hB hT M V D hM hV hdM hD hbound
  have hz : cutoffPrimitive A B 0 = 0 := by simp [cutoffPrimitive]
  have hn : 0 ≤ W/(B+A*Real.sqrt W) :=
    div_nonneg hW (add_nonneg hB.le (mul_nonneg hA (Real.sqrt_nonneg _)))
  rcases hend with ⟨hl,he⟩|⟨he,hl⟩
  · rw [he,hz,zero_sub,neg_sq] at h
    exact (pow_le_pow_left₀ hn (cutoffPrimitive_lower hA hB hW hl) 2).trans h
  · rw [he,hz,sub_zero] at h
    exact (pow_le_pow_left₀ hn (cutoffPrimitive_lower hA hB hW hl) 2).trans h

end MigrationGeometry

open Lean Elab Command in
run_cmd do
  for (n, _) in (← getEnv).constants do
    if `MigrationGeometry |>.isPrefixOf n then
      for a in (← collectAxioms n) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains a do
          throwError "Unexpected axiom {a} in {n}"
  logInfo "Localized length cost passed standard axiom audit."
