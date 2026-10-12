import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Tactic.Linarith

/-!
The Hilbert-space argument of Proposition 3.3, with an explicit operator domain.
This file proves the abstract implication from orthogonal-complement coercivity.
The coercivity of the paper's differential operator is a separate obligation.
Mathlib's inner product is linear in the second slot, opposite to the paper.
-/
namespace Lemniscate
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

structure NeutralCoerciveOperator (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] where
  domain : Submodule ℂ E
  op : domain →ₗ[ℂ] E
  neutral : domain
  unit_neutral : ‖(neutral : E)‖ = 1
  kills_neutral : op neutral = 0
  gap : ℝ
  gap_pos : 0 < gap
  dissipative : ∀ w : domain, inner ℂ (neutral : E) (w : E) = 0 →
    (inner ℂ (w : E) (op w)).re ≤ -gap * ‖(w : E)‖^2

namespace NeutralCoerciveOperator
variable (A : NeutralCoerciveOperator E)

def remainder (f : A.domain) : A.domain :=
  f - (inner ℂ (A.neutral : E) (f : E)) • A.neutral

theorem inner_neutral_self : inner ℂ (A.neutral : E) (A.neutral : E) = 1 := by
  simp [inner_self_eq_norm_sq_to_K, A.unit_neutral]

theorem remainder_orthogonal (f : A.domain) :
    inner ℂ (A.neutral : E) (A.remainder f : E) = 0 := by
  simp [remainder, inner_sub_right, inner_smul_right, A.unit_neutral]

theorem op_remainder (f : A.domain) : A.op (A.remainder f) = A.op f := by
  simp [remainder, A.kills_neutral]

theorem neutral_orthogonal_remainder (f : A.domain) :
    inner ℂ (A.remainder f : E) (A.neutral : E) = 0 := by
  rw [← inner_conj_symm, A.remainder_orthogonal]
  simp

theorem remainder_zero_of_op_eq_neutral (f : A.domain) (c : ℂ)
    (hf : A.op f = c • (A.neutral : E)) : A.remainder f = 0 := by
  have hd := A.dissipative (A.remainder f) (A.remainder_orthogonal f)
  rw [A.op_remainder, hf, inner_smul_right, A.neutral_orthogonal_remainder] at hd
  simp only [mul_zero, Complex.zero_re] at hd
  have hn : ‖(A.remainder f : E)‖^2 = 0 := by
    nlinarith [sq_nonneg ‖(A.remainder f : E)‖, A.gap_pos]
  apply Subtype.ext
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem kernel_is_neutral (f : A.domain) (hf : A.op f = 0) :
    f = (inner ℂ (A.neutral : E) (f : E)) • A.neutral := by
  have hr := A.remainder_zero_of_op_eq_neutral f 0 (by simpa using hf)
  exact sub_eq_zero.mp hr

theorem no_generalized_neutral (f g : A.domain)
    (hfg : A.op f = (g : E)) (hg : A.op g = 0) : A.op f = 0 := by
  have gform := A.kernel_is_neutral g hg
  have hform : A.op f = (inner ℂ (A.neutral : E) (g : E)) • (A.neutral : E) := by
    calc
      A.op f = (g : E) := hfg
      _ = _ := congrArg (fun v : A.domain => (v : E)) gform
  have hr := A.remainder_zero_of_op_eq_neutral f _ hform
  have fr : f = (inner ℂ (A.neutral : E) (f : E)) • A.neutral := sub_eq_zero.mp hr
  rw [fr]
  simp [A.kills_neutral]

theorem nonzero_eigenvalue_bound (f : A.domain) (lam : ℂ)
    (hf : (f : E) ≠ 0) (hlam : lam ≠ 0) (heig : A.op f = lam • (f : E)) :
    lam.re ≤ -A.gap := by
  have hw : (A.remainder f : E) ≠ 0 := by
    intro hw
    have hr : A.remainder f = 0 := Subtype.ext hw
    have hop : A.op f = 0 := by rw [← A.op_remainder f, hr]; simp
    rw [heig] at hop
    exact hf ((smul_eq_zero.mp hop).resolve_left hlam)
  have hid : inner ℂ (A.remainder f : E) (f : E) =
      inner ℂ (A.remainder f : E) (A.remainder f : E) := by
    change inner ℂ (A.remainder f : E) (f : E) =
      inner ℂ (A.remainder f : E)
        ((f : E) - inner ℂ (A.neutral : E) (f : E) • (A.neutral : E))
    rw [inner_sub_right, inner_smul_right, A.neutral_orthogonal_remainder, mul_zero, sub_zero]
  have hd := A.dissipative (A.remainder f) (A.remainder_orthogonal f)
  have hself : inner ℂ (A.remainder f : E) (A.remainder f : E) =
      ((‖(A.remainder f : E)‖^2 : ℝ) : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K]
  rw [A.op_remainder, heig, inner_smul_right, hid, hself] at hd
  have hbound : lam.re*‖(A.remainder f : E)‖^2 ≤ -A.gap*‖(A.remainder f : E)‖^2 := by
    simpa only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] using hd
  have hpos : 0 < ‖(A.remainder f : E)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  nlinarith

end NeutralCoerciveOperator
end Lemniscate
