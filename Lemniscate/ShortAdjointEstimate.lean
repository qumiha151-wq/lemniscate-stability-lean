import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The short adjoint argument uses a weighted residual, rather than an H4
error estimate.  This module proves its Hilbert-space and real-arithmetic
steps.  The concrete eight-mode residual and Fourier normalization must
still be connected to these statements by their own arithmetic proof.
No old even-sector Bloch certificate is imported here.
-/

namespace Lemniscate
noncomputable section

/-- Convex combination of the unchanged sine coercivity and Gårding bound. -/
theorem short_adjoint_weighted_coercivity
    (r a c E : ℝ) (hr : (7177 / 10000 : ℝ) ≤ r)
    (hgap : 75 * a ^ 2 ≤ E)
    (hgarding : 2 * r ^ 2 * c ^ 2 - (1719 / 8 : ℝ) * a ^ 2 ≤ E) :
    (13 / 100 : ℝ) * c ^ 2 + (75 / 2 : ℝ) * a ^ 2 ≤ E := by
  have hr0 : 0 ≤ r := by linarith
  have hr2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7177 / 10000) hr 2
  have hc : (13 / 100 : ℝ) ≤ (32 / 125 : ℝ) * r ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg c)
  nlinarith [sq_nonneg a]

/-- Weighted Cauchy--Schwarz after the residual has been represented in the
weighted Hilbert space.  `residual` is the weighted dual vector, not the
unweighted L2 residual. -/
theorem short_adjoint_weighted_residual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (w residual : H) (energy η : ℝ)
    (henergy : ‖w‖ ^ 2 ≤ energy)
    (hgreen : energy = (inner ℂ w residual).re)
    (hresidual : ‖residual‖ ≤ η) : ‖w‖ ≤ η := by
  have hc : energy ≤ ‖w‖ * ‖residual‖ := by
    rw [hgreen]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm w residual)
  have hm := mul_le_mul_of_nonneg_left hresidual (norm_nonneg w)
  by_cases hz : ‖w‖ = 0
  · rw [hz]
    exact (norm_nonneg residual).trans hresidual
  · have hp : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hz)
    nlinarith

/-- The joint weighted control and weak integration by parts give all the
low-order sum norms used by the new adjoint certificate. -/
theorem short_adjoint_sobolev_bounds
    (a b c W η : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hW : 0 ≤ W) (hη : W ≤ η)
    (hweighted : (13 / 100 : ℝ) * c ^ 2 + (75 / 2 : ℝ) * a ^ 2 ≤ W ^ 2)
    (hweak : b ^ 2 ≤ a * c) :
    a ≤ η / 6 ∧ b ≤ η / 2 ∧ c ≤ (25 / 9 : ℝ) * η ∧
      a + b ≤ (2 / 3 : ℝ) * η ∧
      a + b + c ≤ (31 / 9 : ℝ) * η := by
  have hη0 : 0 ≤ η := hW.trans hη
  have hsq : W ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hW hη 2
  have hprod : 4 * a * c ≤
      (13 / 100 : ℝ) * c ^ 2 + (75 / 2 : ℝ) * a ^ 2 := by
    nlinarith [sq_nonneg (13*c-200*a), sq_nonneg a]
  have h0 : a ≤ η / 6 := by nlinarith [sq_nonneg c]
  have h1 : b ≤ η / 2 := by nlinarith
  have h2 : c ≤ (25 / 9 : ℝ) * η := by nlinarith [sq_nonneg a]
  exact ⟨h0, h1, h2, by linarith, by linarith⟩

/-- Explicit consequences for the preferred eight-mode weighted residual. -/
theorem short_adjoint_eight_mode_sobolev
    (a b c W : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hW : 0 ≤ W) (hresidual : W < (1 / 200000 : ℝ))
    (hweighted : (13 / 100 : ℝ) * c ^ 2 + (75 / 2 : ℝ) * a ^ 2 ≤ W ^ 2)
    (hweak : b ^ 2 ≤ a * c) :
    a + b < (1 / 300000 : ℝ) ∧
      a + b + c < (31 / 1800000 : ℝ) := by
  obtain ⟨_, _, _, h1, h2⟩ :=
    short_adjoint_sobolev_bounds a b c W W ha hb hc hW le_rfl hweighted hweak
  constructor <;> linarith

def shortKernelError : ℝ := 1 / 160000
def shortAdjointError : ℝ := 1 / 200000

/-- Coefficients converting monomials on [0,1/2] to quartic Bernstein
control values. -/
def shortBernsteinPower (j k : Fin 5) : ℝ :=
  (Nat.choose j.val k.val : ℝ) / (Nat.choose 4 k.val : ℝ) * (1 / 2 : ℝ) ^ k.val

theorem short_bernstein_power_bounds (j : Fin 5) :
    0 ≤ shortBernsteinPower j 1 ∧ shortBernsteinPower j 1 ≤ 1/2 ∧
    0 ≤ shortBernsteinPower j 2 ∧ shortBernsteinPower j 2 ≤ 1/4 ∧
    0 ≤ shortBernsteinPower j 3 ∧ shortBernsteinPower j 3 ≤ 1/8 := by
  fin_cases j <;> norm_num [shortBernsteinPower, Nat.choose]

/-- The component form errors arising from the rank-one telescope. -/
def shortAdjointComponentError (j : Fin 4) : ℝ :=
  match j.val with
  | 0 => 198 * shortKernelError
  | 1 => 70 * ((7/3:ℝ)*shortKernelError+4*shortAdjointError)
  | 2 => 45 * ((7/3:ℝ)*shortKernelError+4*shortAdjointError)
  | _ => 5 * ((7/3:ℝ)*shortKernelError+4*shortAdjointError)

/-- The five Bernstein control forms have a common error smaller than 1/125.
The expression includes the constant off-diagonal pieces created by the
exact cancellation of the rotational factors. -/
theorem short_adjoint_bernstein_constants (j : Fin 5) :
    shortAdjointComponentError 0 +
      (1+shortBernsteinPower j 1)*shortAdjointComponentError 1 +
      (1+shortBernsteinPower j 1+shortBernsteinPower j 2)*shortAdjointComponentError 2 +
      (shortBernsteinPower j 2+shortBernsteinPower j 3)*shortAdjointComponentError 3 <
        (1/125:ℝ) := by
  fin_cases j <;>
    norm_num [shortBernsteinPower, shortAdjointComponentError,
      shortKernelError, shortAdjointError, Nat.choose]

theorem short_adjoint_bernstein_common_bound :
    shortAdjointComponentError 0 +
      (3/2:ℝ)*shortAdjointComponentError 1 +
      (7/4:ℝ)*shortAdjointComponentError 2 +
      (3/8:ℝ)*shortAdjointComponentError 3 = (9801/1280000:ℝ) := by
  norm_num [shortAdjointComponentError, shortKernelError, shortAdjointError]

/-- Absorption after the one finite shear; the Hadamard change is unitary. -/
theorem short_adjoint_shear_bound (E N : ℝ) (hN : 0 ≤ N)
    (hE : |E| ≤ (9801/1280000:ℝ)*((7/6:ℝ)*N)) :
    |E| ≤ (22869/2560000:ℝ)*N ∧
      |E| ≤ (1/100:ℝ)*N := by
  constructor
  · nlinarith
  · nlinarith

theorem short_adjoint_shear_coefficient :
    (7/6:ℝ)*(9801/1280000:ℝ) < (1/100:ℝ) := by norm_num

/-- The complete V-form error is absorbed on the diagonal of the two-block
estimate, not subtracted from a Schur-complement remainder. -/
theorem short_adjoint_schur_constants :
    (7/100:ℝ)*(31/25:ℝ) > (1/4:ℝ)^2 := by norm_num

end
end Lemniscate
