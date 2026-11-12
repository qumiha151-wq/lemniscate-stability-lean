import CentroidEscape.WeightedExpansion
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Convert

/-!
# Derivatives of the actual weighted shooting field

These are derivatives of the unclipped polynomial field. No global
differentiability of the coordinate-clipped field is asserted.
-/
namespace CentroidEscape
noncomputable section
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem weightedField_smooth : ContDiff ℝ ∞ weightedField := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [weightedField] <;> fun_prop

lemma weightedField_line_expansion (a u : WeightedState) (t : ℝ) :
    weightedField (a+t • u) = weightedField a+t • weightedLinear a u+
      t^2 • weightedBilinear a u u+t^3 • weightedTrilinear u u u := by
  rw [weightedField_expansion, weightedLinear_smul,
    weightedBilinear_smul_left, weightedBilinear_smul_right,
    weightedTrilinear_smul_first, weightedTrilinear_smul_second,
    weightedTrilinear_smul_third]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem weightedField_line_hasDerivAt (a u : WeightedState) :
    HasDerivAt (fun t : ℝ => weightedField (a+t • u)) (weightedLinear a u) 0 := by
  have h := (((hasDerivAt_const (0:ℝ) (weightedField a)).add
    ((hasDerivAt_id (0:ℝ)).smul_const (weightedLinear a u))).add
    (((hasDerivAt_id (0:ℝ)).pow 2).smul_const (weightedBilinear a u u))).add
    (((hasDerivAt_id (0:ℝ)).pow 3).smul_const (weightedTrilinear u u u))
  convert! h using 1
  · funext t
    exact weightedField_line_expansion a u t
  · simp

theorem weightedField_fderiv_apply (a u : WeightedState) :
    fderiv ℝ weightedField a u = weightedLinear a u := by
  have hg : HasDerivAt (fun t : ℝ => a+t • u) u 0 := by
    convert! (hasDerivAt_const (0:ℝ) a).add
      ((hasDerivAt_id (0:ℝ)).smul_const u) using 1; simp
  have hf := (weightedField_smooth.differentiable (by simp) a).hasFDerivAt
  have hc := hf.comp_hasDerivAt_of_eq 0 hg (by simp)
  exact hc.unique (weightedField_line_hasDerivAt a u)

theorem weightedField_fderiv_bound {a : WeightedState} (ha : a ∈ weightedTube) :
    ‖fderiv ℝ weightedField a‖ ≤ 8 := by
  apply (fderiv ℝ weightedField a).opNorm_le_bound (by norm_num)
  intro u
  rw [weightedField_fderiv_apply]
  exact weightedLinear_bound ha u

theorem weightedField_taylor_remainder {a : WeightedState} (ha : a ∈ weightedTube)
    (u : WeightedState) :
    ‖weightedField (a+u)-weightedField a-fderiv ℝ weightedField a u‖ ≤
      22*‖u‖^2+32*‖u‖^3 := by
  rw [weightedField_fderiv_apply, weightedField_expansion]
  have he : weightedField a+weightedLinear a u+weightedBilinear a u u+
      weightedTrilinear u u u-weightedField a-weightedLinear a u =
      weightedBilinear a u u+weightedTrilinear u u u := by abel
  rw [he]
  have hn := norm_add_le (weightedBilinear a u u) (weightedTrilinear u u u)
  nlinarith [weightedBilinear_bound ha u u, weightedTrilinear_bound u u u]

def weightedSecond (a u v : WeightedState) : WeightedState :=
  weightedBilinear a u v+weightedBilinear a v u

lemma weightedLinear_smooth (v : WeightedState) :
    ContDiff ℝ ∞ (fun a => weightedLinear a v) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [weightedLinear] <;> fun_prop

lemma weightedLinear_line_expansion (a u v : WeightedState) (t : ℝ) :
    weightedLinear (a+t • u) v = weightedLinear a v+t • weightedSecond a u v+
      t^2 • ((3:ℝ) • weightedTrilinear u u v) := by
  ext i
  fin_cases i <;> simp [weightedLinear, weightedSecond, weightedBilinear,
    weightedTrilinear, smul_eq_mul] <;> ring

lemma weightedLinear_line_hasDerivAt (a u v : WeightedState) :
    HasDerivAt (fun t : ℝ => weightedLinear (a+t • u) v) (weightedSecond a u v) 0 := by
  have h := ((hasDerivAt_const (0:ℝ) (weightedLinear a v)).add
    ((hasDerivAt_id (0:ℝ)).smul_const (weightedSecond a u v))).add
    (((hasDerivAt_id (0:ℝ)).pow 2).smul_const ((3:ℝ) • weightedTrilinear u u v))
  convert! h using 1
  · funext t
    exact weightedLinear_line_expansion a u v t
  · simp

theorem weightedLinear_fderiv_apply (a u v : WeightedState) :
    fderiv ℝ (fun x => weightedLinear x v) a u = weightedSecond a u v := by
  have hg : HasDerivAt (fun t : ℝ => a+t • u) u 0 := by
    convert! (hasDerivAt_const (0:ℝ) a).add
      ((hasDerivAt_id (0:ℝ)).smul_const u) using 1; simp
  have hf := ((weightedLinear_smooth v).differentiable (by simp) a).hasFDerivAt
  have hc := hf.comp_hasDerivAt_of_eq 0 hg (by simp)
  exact hc.unique (weightedLinear_line_hasDerivAt a u v)

theorem weightedField_second_fderiv_apply (a u v : WeightedState) :
    fderiv ℝ (fderiv ℝ weightedField) a u v = weightedSecond a u v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ weightedField) a :=
    (weightedField_smooth.fderiv_right (m := 1)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiable (by norm_num) a
  have hh := fderiv_clm_apply (c := fderiv ℝ weightedField)
    (u := fun _ : WeightedState => v) hd (differentiableAt_const v)
  have he : (fun x => fderiv ℝ weightedField x v) = (fun x => weightedLinear x v) :=
    funext (fun x => weightedField_fderiv_apply x v)
  rw [he] at hh
  have hu := congrArg (fun L => L u) hh
  have hconst : fderiv ℝ (fun _ : WeightedState => v) a = 0 :=
    (hasFDerivAt_const v a).fderiv
  simpa only [weightedLinear_fderiv_apply, add_apply,
    ContinuousLinearMap.comp_apply, hconst, zero_apply,
    map_zero, zero_add, ContinuousLinearMap.flip_apply] using hu.symm

theorem weightedSecond_bound {a : WeightedState} (ha : a ∈ weightedTube)
    (u v : WeightedState) : ‖weightedSecond a u v‖ ≤ 44*‖u‖*‖v‖ := by
  have hh := norm_add_le (weightedBilinear a u v) (weightedBilinear a v u)
  unfold weightedSecond
  nlinarith [weightedBilinear_bound ha u v, weightedBilinear_bound ha v u]

theorem weightedField_second_fderiv_bound {a : WeightedState} (ha : a ∈ weightedTube) :
    ‖fderiv ℝ (fderiv ℝ weightedField) a‖ ≤ 44 := by
  apply (fderiv ℝ (fderiv ℝ weightedField) a).opNorm_le_bound (by norm_num)
  intro u
  apply ((fderiv ℝ (fderiv ℝ weightedField) a) u).opNorm_le_bound (by positivity)
  intro v
  rw [weightedField_second_fderiv_apply]
  exact weightedSecond_bound ha u v

lemma weightedTube_convex : Convex ℝ weightedTube := by
  intro a ha b hb c d hc hd hcd i hi
  change |c*a i+d*b i| ≤ tubeRadius i
  calc
    |c*a i+d*b i| ≤ |c*a i|+|d*b i| := abs_add_le _ _
    _ = c*|a i|+d*|b i| := by rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hd]
    _ ≤ c*tubeRadius i+d*tubeRadius i :=
      add_le_add (mul_le_mul_of_nonneg_left (ha i hi) hc)
        (mul_le_mul_of_nonneg_left (hb i hi) hd)
    _ = tubeRadius i := by rw [← add_mul, hcd, one_mul]

theorem weightedField_fderiv_lipschitz :
    LipschitzOnWith 44 (fderiv ℝ weightedField) weightedTube := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro a _
    exact (weightedField_smooth.fderiv_right (m := 1)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiable (by norm_num) a
  · intro a ha
    exact_mod_cast weightedField_second_fderiv_bound ha
  · exact weightedTube_convex

end
end CentroidEscape

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
  logInfo m!"Weighted-derivative audit passed: {checked} declarations; standard axioms only."
