module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
# A kernel-checked rational enclosure of the actual real number pi

Machin's identity and the alternating arctangent series give the bounds.
All finite arithmetic below is checked by `norm_num`, not native evaluation.
This module supplies a constant enclosure only; it asserts no shooting root.
-/

namespace SolitonClassification.Rotating.CertifiedPi

open Finset Filter
open scoped Topology

noncomputable def atanPartial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, (-1 : ℝ) ^ j * (x ^ (2 * j + 1) / (2 * j + 1 : ℕ))

theorem atanTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun j : ℕ => x ^ (2 * j + 1) / (2 * j + 1 : ℕ)) := by
  intro i j hij
  refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
  · exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  · exact_mod_cast (show 2 * i + 1 ≤ 2 * j + 1 by omega)

theorem atanPartial_even_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    atanPartial x (2 * n) ≤ Real.arctan x := by
  have hx : ‖x‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  have ht := (Real.hasSum_arctan hx).tendsto_sum_nat
  simp only [mul_div_assoc] at ht
  exact Antitone.alternating_series_le_tendsto ht (atanTerm_antitone hx0 hx1.le) n

theorem atanPartial_odd_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    Real.arctan x ≤ atanPartial x (2 * n + 1) := by
  have hx : ‖x‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  have ht := (Real.hasSum_arctan hx).tendsto_sum_nat
  simp only [mul_div_assoc] at ht
  exact Antitone.tendsto_le_alternating_series ht (atanTerm_antitone hx0 hx1.le) n

/-- The lower endpoint, truncated after 64 decimal places. -/
def lower : ℚ :=
  31415926535897932384626433832795028841971693993751058209749445923 / 10 ^ 64

def upper : ℚ := lower + 1 / 10 ^ 64

def center : ℚ := (lower + upper) / 2

def radius : ℚ := 1 / (2 * 10 ^ 64)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem lower_lt_machin_partial :
    (lower : ℝ) < 16 * atanPartial (5 : ℝ)⁻¹ 48 -
      4 * atanPartial (239 : ℝ)⁻¹ 17 := by
  norm_num [lower, atanPartial, Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem machin_partial_lt_upper :
    16 * atanPartial (5 : ℝ)⁻¹ 49 -
      4 * atanPartial (239 : ℝ)⁻¹ 16 < (upper : ℝ) := by
  norm_num [upper, lower, atanPartial, Finset.sum_range_succ]

theorem lower_lt_pi : (lower : ℝ) < Real.pi := by
  have h5 := atanPartial_even_le (x := (5 : ℝ)⁻¹) (by norm_num) (by norm_num) 24
  have h239 := atanPartial_odd_ge (x := (239 : ℝ)⁻¹) (by norm_num) (by norm_num) 8
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hn := lower_lt_machin_partial
  norm_num at h5 h239
  linarith

theorem pi_lt_upper : Real.pi < (upper : ℝ) := by
  have h5 := atanPartial_odd_ge (x := (5 : ℝ)⁻¹) (by norm_num) (by norm_num) 24
  have h239 := atanPartial_even_le (x := (239 : ℝ)⁻¹) (by norm_num) (by norm_num) 8
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hn := machin_partial_lt_upper
  norm_num at h5 h239
  linarith

theorem enclosure : (lower : ℝ) < Real.pi ∧ Real.pi < (upper : ℝ) :=
  ⟨lower_lt_pi, pi_lt_upper⟩

theorem radius_pos : 0 < (radius : ℝ) := by
  norm_num [radius]

theorem abs_pi_sub_center_lt : |Real.pi - (center : ℝ)| < (radius : ℝ) := by
  rw [abs_lt]
  have hlo := lower_lt_pi
  have hhi := pi_lt_upper
  norm_num [center, upper, radius, lower] at *
  constructor <;> linarith

theorem radius_lt_ten_neg_sixty : (radius : ℝ) < 1 / (10 : ℝ) ^ 60 := by
  norm_num [radius]

theorem abs_pi_sub_center_le_ten_neg_sixty :
    |Real.pi - (center : ℝ)| ≤ 1 / (10 : ℝ) ^ 60 :=
  (abs_pi_sub_center_lt.trans radius_lt_ten_neg_sixty).le

end SolitonClassification.Rotating.CertifiedPi

#print axioms SolitonClassification.Rotating.CertifiedPi.enclosure
#print axioms SolitonClassification.Rotating.CertifiedPi.abs_pi_sub_center_lt

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating.CertifiedPi).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "CertifiedPi axiom audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"CertifiedPi axiom audit passed for {count} declarations."
