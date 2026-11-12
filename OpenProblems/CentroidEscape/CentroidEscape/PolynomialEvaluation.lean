import CentroidEscape.PolynomialResidual
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace CentroidEscape
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

def majorantPoly (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 161, (majorantCoeff n : ℝ)*s^n

def majorantPolyDeriv (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 161, (majorantCoeff n : ℝ)*n*s^(n-1)

lemma majorantPoly_hasDerivAt (s : ℝ) :
    HasDerivAt majorantPoly (majorantPolyDeriv s) s := by
  unfold majorantPoly majorantPolyDeriv
  apply HasDerivAt.fun_sum
  intro n hn
  convert! ((hasDerivAt_id s).pow n).const_mul (majorantCoeff n : ℝ) using 1 <;>
    first | rfl | (simp only [id_eq, Pi.pow_apply, mul_one] <;> ring)

lemma majorant_rational_value :
    (∑ n ∈ Finset.range 161, (majorantCoeff n : ℚ)*(1/100:ℚ)^n) = majorantValue := by
  decide +kernel

lemma majorant_rational_derivative :
    (∑ n ∈ Finset.range 161, (majorantCoeff n : ℚ)*n*(1/100:ℚ)^(n-1)) =
      majorantDerivative := by
  decide +kernel

lemma majorantPoly_value : majorantPoly (1/100) = (majorantValue : ℝ) := by
  have hh := congrArg (fun q : ℚ => (q : ℝ)) majorant_rational_value
  simpa [majorantPoly] using hh

lemma majorantPoly_derivative_value :
    deriv majorantPoly (1/100) = (majorantDerivative : ℝ) := by
  rw [(majorantPoly_hasDerivAt _).deriv]
  have hh := congrArg (fun q : ℚ => (q : ℝ)) majorant_rational_derivative
  simpa [majorantPolyDeriv] using hh

/-- The checked rational residual is the actual finite-polynomial differential
residual at the maximal step. Uniform residual bounds remain to be derived. -/
theorem polynomialResidual_is_derivative_residual :
    2*(majorantPoly (1/100))^3 - deriv majorantPoly (1/100)/3 =
      (polynomialResidual : ℝ) := by
  rw [majorantPoly_value, majorantPoly_derivative_value]
  simp [polynomialResidual]

end
end CentroidEscape

#print axioms CentroidEscape.polynomialResidual_is_derivative_residual
