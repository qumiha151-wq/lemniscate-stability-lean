import Lemniscate.NeutralMode
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! An exact normalized adjoint neutral vector from the inverse of P-A.
The inverse is supplied with both identities on the original operator domain;
the next application obtains it from the proved periodic Fredholm alternative. -/
namespace Lemniscate.NeutralCoerciveOperator
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : NeutralCoerciveOperator E)

theorem neutral_rank_one_shift_kernel (u : A.domain)
    (hu : (inner ℂ (A.neutral : E) (u : E)) • (A.neutral : E)-A.op u = 0) :
    (u : E) = 0 := by
  have hAu : A.op u = (inner ℂ (A.neutral : E) (u : E)) • (A.neutral : E) :=
    (sub_eq_zero.mp hu).symm
  have hr := A.remainder_zero_of_op_eq_neutral u _ hAu
  have huf : u = (inner ℂ (A.neutral : E) (u : E)) • A.neutral := sub_eq_zero.mp hr
  calc
    (u : E) = (inner ℂ (A.neutral : E) (u : E)) • (A.neutral : E) :=
      congrArg (fun w : A.domain => (w : E)) huf
    _ = A.op u := hAu.symm
    _ = 0 := by rw [huf, map_smul, A.kills_neutral, smul_zero]

theorem exists_unique_adjoint_neutral_of_inverse (R : E →L[ℂ] E)
    (hright : ∀ f : E, ∃ u : A.domain,
      (inner ℂ (A.neutral : E) (u : E)) • (A.neutral : E)-A.op u = f)
    (hleft : ∀ u : A.domain,
      R ((inner ℂ (A.neutral : E) (u : E)) • (A.neutral : E)-A.op u) = (u : E)) :
    ∃! ψ : E, inner ℂ ψ (A.neutral : E) = 1 ∧ ∀ u : A.domain, inner ℂ ψ (A.op u) = 0 := by
  have hRb : R (A.neutral : E) = (A.neutral : E) := by
    have hb := hleft A.neutral
    simpa only [A.inner_neutral_self, one_smul, A.kills_neutral, sub_zero] using hb
  let ψ := R.adjoint (A.neutral : E)
  have hn : inner ℂ ψ (A.neutral : E) = 1 := by
    rw [show inner ℂ ψ (A.neutral : E) = inner ℂ (A.neutral : E) (R (A.neutral : E)) from
      R.adjoint_inner_left _ _, hRb, A.inner_neutral_self]
  have hz (u : A.domain) : inner ℂ ψ (A.op u) = 0 := by
    have hu := hleft u
    rw [map_sub, map_smul, hRb] at hu
    have hi := congrArg (fun x : E => inner ℂ (A.neutral : E) x) hu
    simp only [inner_sub_right, inner_smul_right, A.inner_neutral_self, mul_one] at hi
    rw [show inner ℂ ψ (A.op u) = inner ℂ (A.neutral : E) (R (A.op u)) from
      R.adjoint_inner_left _ _]
    linear_combination -hi
  refine ⟨ψ, ⟨hn, hz⟩, ?_⟩
  intro ψ' hψ'
  apply ext_inner_right ℂ
  intro f
  obtain ⟨u, hu⟩ := hright f
  rw [← hu]
  simp only [inner_sub_right, inner_smul_right, hψ'.1, hψ'.2, hn, hz, mul_one, sub_zero]

end Lemniscate.NeutralCoerciveOperator
