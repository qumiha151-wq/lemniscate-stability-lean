import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Polynomial Function Set
open scoped BigOperators
namespace ClosedSimilarity.Holonomic

/-- Spatial translates of the same periodic jet provide infinitely many roots.
Consequently every evaluation of the polynomial coefficients gives a
constant-coefficient identity for the same periodic jet. -/
theorem freeze_coefficients {P : ℝ} (hp : 0 < P) (J : Finset ℕ)
    (u : ℕ → ℝ → ℂ) (p : ℕ → Polynomial ℂ) (per : ∀ j ∈ J, Periodic (u j) P)
    (ode : ∀ s : ℝ, ∑ j ∈ J, (p j).eval (s : ℂ)*u j s = 0) (z : ℂ) (s : ℝ) :
    ∑ j ∈ J, (p j).eval z*u j s = 0 := by
  classical
  let q := ∑ j ∈ J, C (u j s) * p j
  let sample := fun n : ℕ => (↑(s + (n:ℝ)*P) : ℂ)
  have inj : Injective sample := by
    intro n m eq
    have t : s+(n:ℝ)*P = s+(m:ℝ)*P := Complex.ofReal_injective eq
    have x : (n:ℝ) = (m:ℝ) := mul_right_cancel₀ hp.ne' (add_left_cancel t)
    exact_mod_cast x
  have vanishes : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective inj).mono
    rintro _ ⟨n,rfl⟩
    change q.eval (sample n) = 0
    rw [show q.eval (sample n) = ∑ j ∈ J, (p j).eval (sample n)*u j (s+(n:ℝ)*P) by
      unfold q
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
      apply Finset.sum_congr rfl
      intro j hj
      have h := ((per j hj).nsmul n) s
      rw [nsmul_eq_mul] at h
      rw [h,mul_comm]]
    exact ode _
  have val := congrArg (Polynomial.eval z) vanishes
  simpa only [q,Polynomial.eval_finsetSum, Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_zero,
    mul_comm (u _ s)] using val

/-- A periodic polynomial-coefficient differential relation has a nonzero
ordinary characteristic polynomial, independent of position. -/
theorem frozen_annihilator {P : ℝ} (hp : 0 < P) (J : Finset ℕ)
    (u : ℕ → ℝ → ℂ) (p : ℕ → Polynomial ℂ) (per : ∀ j ∈ J, Periodic (u j) P)
    (nonzero : ∃ j ∈ J, p j ≠ 0)
    (ode : ∀ s : ℝ, ∑ j ∈ J, (p j).eval (s : ℂ)*u j s = 0) :
    ∃ c : ℕ → ℂ, (∃ j ∈ J, c j ≠ 0) ∧ ∀ s : ℝ, ∑ j ∈ J, c j*u j s = 0 := by
  obtain ⟨j,hj,nz⟩ := nonzero
  have existsPoint : ∃ z : ℂ, (p j).eval z ≠ 0 := by
    by_contra! h
    apply nz
    apply Polynomial.eq_zero_of_infinite_isRoot
    convert! (Set.infinite_univ : (Set.univ : Set ℂ).Infinite) using 1
    ext z
    simp [Polynomial.IsRoot,h]
  obtain ⟨z,hz⟩ := existsPoint
  exact ⟨fun i => (p i).eval z,⟨j,hj,hz⟩,freeze_coefficients hp J u p per ode z⟩

end ClosedSimilarity.Holonomic
#print axioms ClosedSimilarity.Holonomic.frozen_annihilator

