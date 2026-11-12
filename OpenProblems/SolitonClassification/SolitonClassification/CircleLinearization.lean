import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Lean.Util.CollectAxioms

/-! Actual derivative and imaginary-axis exclusion for a circular support
equilibrium. This is linear algebra, not a formal local nonlinear dynamical
exclusion theorem or a classification of noncircular profiles. -/

namespace ClosedSimilarity.CircleLinearization
noncomputable section

abbrev State := Fin 4 → ℝ

def supportField (a b : ℝ) (z : State) : State :=
  ![z 1, -(1/2)*z 0^3-a*z 2-b*z 3, -z 0*z 3, 1+z 0*z 2]

def circle (K : ℝ) : State := ![K, 0, -K⁻¹, 0]

def jacobian (K b : ℝ) : State →L[ℝ] State :=
  ContinuousLinearMap.pi ![
    ContinuousLinearMap.proj 1,
    (-(3/2)*K^2) • ContinuousLinearMap.proj 0 -
      (K^4/2) • ContinuousLinearMap.proj 2 - b • ContinuousLinearMap.proj 3,
    (-K) • ContinuousLinearMap.proj 3,
    (-K⁻¹) • ContinuousLinearMap.proj 0 + K • ContinuousLinearMap.proj 2]

theorem circle_equilibrium {K : ℝ} (hK : K ≠ 0) (b : ℝ) :
    supportField (K^4/2) b (circle K) = 0 := by
  ext i
  fin_cases i <;> simp [supportField, circle]
  · field_simp
    ring
  · simp [hK]

theorem supportField_hasFDerivAt_circle (K b : ℝ) :
    HasFDerivAt (supportField (K^4/2) b) (jacobian K b) (circle K) := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) 0 (circle K)
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) 1 (circle K)
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) 2 (circle K)
  have h3 := hasFDerivAt_apply (𝕜 := ℝ) 3 (circle K)
  unfold supportField jacobian
  apply hasFDerivAt_pi.2
  intro i
  fin_cases i
  · simpa using h1
  · convert (((h0.pow 3).const_mul (-(1/2 : ℝ))).sub
      (h2.const_mul (K^4/2))).sub (h3.const_mul b) using 1
    all_goals first | rfl | (ext z; simp [circle]; ring)
  · convert (h0.mul h3).neg using 1
      <;> ext z <;> simp [circle]
  · convert (hasFDerivAt_const (1 : ℝ) (circle K)).add (h0.mul h2) using 1
    all_goals first | rfl | (ext z; simp [circle]; ring)

def complexJacobian (K b : ℝ) (z : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![z 1, (-(3/2 : ℂ)*(K:ℂ)^2)*z 0-((K:ℂ)^4/2)*z 2-(b:ℂ)*z 3,
    -(K:ℂ)*z 3, -(K:ℂ)⁻¹*z 0+(K:ℂ)*z 2]

def characteristic (K b : ℝ) (mu : ℂ) : ℂ :=
  mu^4+(5/2:ℂ)*(K:ℂ)^2*mu^2-((b/K:ℝ):ℂ)*mu+2*(K:ℂ)^4

theorem complexJacobian_of_real (K b : ℝ) (z : State) :
    complexJacobian K b (fun i => (z i : ℂ)) = fun i => ((jacobian K b z i : ℝ) : ℂ) := by
  ext i
  fin_cases i <;> simp [complexJacobian, jacobian]

theorem characteristic_imaginary_real_part (K b y : ℝ) :
    (characteristic K b (Complex.I*(y:ℂ))).re =
      (y^2-(5/4:ℝ)*K^2)^2+(7/16:ℝ)*K^4 := by
  simp [characteristic, pow_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem characteristic_imaginary_ne_zero {K : ℝ} (hK : K ≠ 0) (b y : ℝ) :
    characteristic K b (Complex.I*(y:ℂ)) ≠ 0 := by
  intro hz
  have he := characteristic_imaginary_real_part K b y
  rw [hz, Complex.zero_re] at he
  have hk4 : 0 < K^4 := by
    simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero hK) 2
  nlinarith [sq_nonneg (y^2-(5/4:ℝ)*K^2)]

/-- Direct elimination from the actual four linearized equations. In
particular no division by the eigenvalue is used or assumed. -/
theorem characteristic_eq_zero_of_eigenvector {K : ℝ} (hK : K ≠ 0)
    (b : ℝ) {mu : ℂ} {z : Fin 4 → ℂ} (hz : z ≠ 0)
    (heig : complexJacobian K b z = fun i => mu*z i) :
    characteristic K b mu = 0 := by
  have hKC : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have h0 : z 1 = mu*z 0 := by simpa [complexJacobian] using congrFun heig 0
  have h1 : (-(3/2:ℂ)*(K:ℂ)^2)*z 0-((K:ℂ)^4/2)*z 2-(b:ℂ)*z 3 = mu*z 1 := by
    simpa [complexJacobian] using congrFun heig 1
  have h2 : -(K:ℂ)*z 3 = mu*z 2 := by simpa [complexJacobian] using congrFun heig 2
  have h3 : -(K:ℂ)⁻¹*z 0+(K:ℂ)*z 2 = mu*z 3 := by
    simpa [complexJacobian] using congrFun heig 3
  have hq : z 3 = -mu*z 2/(K:ℂ) := by
    apply (eq_div_iff hKC).mpr
    linear_combination -h2
  have hscaled : -z 0+(K:ℂ)^2*z 2 = (K:ℂ)*mu*z 3 := by
    calc
      _ = (K:ℂ)*(-(K:ℂ)⁻¹*z 0+(K:ℂ)*z 2) := by field_simp
      _ = _ := by rw [h3]; ring
  have hk : z 0 = (mu^2+(K:ℂ)^2)*z 2 := by
    linear_combination -hscaled+mu*h2
  have hp : z 2 ≠ 0 := by
    intro hp0
    apply hz
    ext i
    fin_cases i <;> simp [hp0, hq, hk, h0]
  have hpoly : characteristic K b mu*z 2 = 0 := by
    rw [h0, hk, hq] at h1
    dsimp [characteristic]
    push_cast
    linear_combination -h1
  exact (mul_eq_zero.mp hpoly).resolve_right hp

/-- The actual circular Jacobian has no nonzero eigenvector for any
purely imaginary eigenvalue, for either sign of curvature and every real b. -/
theorem no_purely_imaginary_eigenvector {K : ℝ} (hK : K ≠ 0) (b y : ℝ)
    {z : Fin 4 → ℂ} (heig : complexJacobian K b z = fun i => (Complex.I*(y:ℂ))*z i) :
    z = 0 := by
  by_contra hz
  exact characteristic_imaginary_ne_zero hK b y
    (characteristic_eq_zero_of_eigenvector hK b hz heig)

end
end ClosedSimilarity.CircleLinearization

#print axioms ClosedSimilarity.CircleLinearization.supportField_hasFDerivAt_circle
#print axioms ClosedSimilarity.CircleLinearization.no_purely_imaginary_eigenvector

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`ClosedSimilarity.CircleLinearization).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "CircleLinearization audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  unless checked > 0 do
    throwError "CircleLinearization audit checked no declarations"
  logInfo m!"CircleLinearization audit passed: {checked} declarations; standard axioms only."
