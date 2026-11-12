import CentroidEscape.PolynomialResidual
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import CentroidEscape.ValidatedIntegration
import Lean.Util.CollectAxioms

/-!
# Exact arithmetic budgets for the metric method at Taylor order 60

The residual here is the finite scalar polynomial residual 2*u^3-u'/3,
not an infinite-series tail. The file certifies its numerical budget and
the proposed shooting Hessian budget. Applying these numbers to the actual
flow still requires the metric propagation and parameter variation theorems.
-/
namespace CentroidEscape.MetricStability
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def majorant60Denominator : ℕ := 100^60
def majorant60Numerator : ℕ :=
  (List.range 61).foldl (fun a n => a+majorantCoeff n*100^(60-n)) 0
def majorant60DerivativeNumerator : ℕ :=
  (List.range 61).foldl (fun a n => a+n*majorantCoeff n*100^(60-n)) 0
def majorant60Value : ℚ := (majorant60Numerator:ℚ)/majorant60Denominator
def majorant60Derivative : ℚ :=
  100*(majorant60DerivativeNumerator:ℚ)/majorant60Denominator
def finiteResidual60 : ℚ := 2*majorant60Value^3-majorant60Derivative/3

theorem finiteResidual60_positive : 0<finiteResidual60 := by decide +kernel

/-- 25/23 retains a safe local exponential factor from the finite-residual route. -/
theorem finiteResidual60_global_budget :
    (34:ℚ)*750*4000000*(25/23)*(1/100)*finiteResidual60 < 1/10^43 := by
  decide +kernel

theorem metric_exp_budget {T : ℝ} (hT : T≤15/2) :
    Real.exp ((39/20)*T)<4000000 := by
  have happrox := Real.exp_bound' (x := (1:ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  have hone : Real.exp 1≤(11/4:ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at happrox
    linarith
  calc
    Real.exp ((39/20)*T) ≤ Real.exp 15 := Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp 1)^15 := by simp
    _ ≤ (11/4:ℝ)^15 := pow_le_pow_left₀ (Real.exp_pos _).le hone 15
    _ < 4000000 := by norm_num

theorem metric_hessian_arithmetic_budget :
    (5/2:ℚ)*((205/52)*4000000*(4000000-1)+(117/4)*4000000+135)<2*10^14 := by
  decide +kernel

theorem metric_newton_arithmetic_budget :
    (1/10^9:ℚ)+2*(3*((2*10^14)*(1/10^25)/2)+(2*10^14)*(1/10^28))<2/10^9 := by
  decide +kernel

end
end CentroidEscape.MetricStability

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.MetricStability).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Metric arithmetic budget audit passed for {checked} declarations."
