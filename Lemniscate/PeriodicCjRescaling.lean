import Lemniscate.NormalGraphCjEstimate
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Data.Real.Pointwise

/-! The exact derivative weights and standard C^j bound under a nonzero
linear change of the curve parameter. Total-derivative identities make
regularity and periodicity assumptions unnecessary for this transport.

-/
noncomputable section
namespace Lemniscate
open Set
open scoped Pointwise BigOperators

private theorem iterated_deriv_parameter_rescaling
    (E : ℝ → ℂ) (a : ℝ) (i : ℕ) :
    iteratedDeriv i (fun s => E (a*s))=
      fun s => a^i • iteratedDeriv i E (a*s) := by
  induction i with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_smul]
  | succ i ih =>
      rw [iteratedDeriv_succ,ih]
      funext s
      rw [deriv_fun_const_smul_field,deriv_comp_mul_left]
      simp only [smul_smul,pow_succ,iteratedDeriv_succ]

private theorem norm_derivative_sup_rescaling
    (E : ℝ → ℂ) (a : ℝ) (ha : a≠0) (i : ℕ) :
    sSup (Set.range (fun s : ℝ => ‖iteratedDeriv i (fun x => E (a*x)) s‖))=
      |a|^i*sSup (Set.range (fun x : ℝ => ‖iteratedDeriv i E x‖)) := by
  have hnorm (s : ℝ) : ‖iteratedDeriv i (fun x => E (a*x)) s‖=
      |a|^i*‖iteratedDeriv i E (a*s)‖ := by
    rw [iterated_deriv_parameter_rescaling]
    simp only [norm_smul,norm_pow,Real.norm_eq_abs]
  have hrange : Set.range (fun s : ℝ => ‖iteratedDeriv i (fun x => E (a*x)) s‖)=
      |a|^i • Set.range (fun x : ℝ => ‖iteratedDeriv i E x‖) := by
    ext y
    constructor
    · rintro ⟨s,rfl⟩
      apply Set.mem_smul_set.mpr
      refine ⟨‖iteratedDeriv i E (a*s)‖,⟨a*s,rfl⟩,?_⟩
      exact (hnorm s).symm
    · intro hy
      obtain ⟨v,⟨x,rfl⟩,hy⟩ := Set.mem_smul_set.mp hy
      refine ⟨x/a,?_⟩
      have harg : a*(x/a)=x := by field_simp [ha] <;> ring
      change ‖iteratedDeriv i (fun u => E (a*u)) (x/a)‖=y
      rw [hnorm,harg]
      exact hy
  rw [hrange]
  simpa only [smul_eq_mul] using
    Real.sSup_smul_of_nonneg (pow_nonneg (abs_nonneg a) i)
      (Set.range (fun x : ℝ => ‖iteratedDeriv i E x‖))

/-- A nonzero parameter dilation gives the exact derivative weights, and
multiplies the standard C^j norm by at most max(1,|a|)^j. In particular this
transports the spectral x-coordinate estimate to physical arclength when
a=sqrt(2). No extra smoothness or periodicity hypothesis is needed. -/
theorem periodic_cj_norm_rescaling
    (j : ℕ) (E : ℝ → ℂ) (a : ℝ) (ha : a≠0) :
    periodicCjNorm j (fun s => E (a*s))=
        ∑ i : Fin (j+1), |a|^i.val*
          sSup (Set.range (fun x : ℝ => ‖iteratedDeriv i.val E x‖)) ∧
      periodicCjNorm j (fun s => E (a*s))≤
        (max 1 |a|)^j*periodicCjNorm j E := by
  have heq : periodicCjNorm j (fun s => E (a*s))=
      ∑ i : Fin (j+1), |a|^i.val*
        sSup (Set.range (fun x : ℝ => ‖iteratedDeriv i.val E x‖)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact norm_derivative_sup_rescaling E a ha i.val
  refine ⟨heq,?_⟩
  rw [heq]
  calc
    _≤∑ i : Fin (j+1), (max 1 |a|)^j*
        sSup (Set.range (fun x : ℝ => ‖iteratedDeriv i.val E x‖)) := by
      apply Finset.sum_le_sum
      intro i _
      have hpow : |a|^i.val≤(max 1 |a|)^j :=
        (pow_le_pow_left₀ (abs_nonneg a) (le_max_right 1 |a|) i.val).trans
          (pow_le_pow_right₀ (le_max_left 1 |a|) (Nat.le_of_lt_succ i.isLt))
      apply mul_le_mul_of_nonneg_right hpow
      apply Real.sSup_nonneg
      rintro _ ⟨x,rfl⟩
      exact norm_nonneg _
    _=(max 1 |a|)^j*periodicCjNorm j E := by
      rw [periodicCjNorm,Finset.mul_sum]

end Lemniscate
