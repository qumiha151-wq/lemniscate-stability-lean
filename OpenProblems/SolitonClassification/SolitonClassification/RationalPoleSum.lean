import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open Polynomial Lagrange
open scoped Polynomial ComplexConjugate
namespace ClosedSimilarity.RationalArclength

/-- Partial fractions for a quotient with simple poles and bounded numerator degree.
The numerator left after removing the constant part is interpolated at every pole. -/
theorem partial_fraction_nonroot (S : Finset ℂ) (A B : ℂ[X]) (b limitValue : ℂ)
    (hb : b ≠ 0) (factor : B=C b * nodal S id)
    (proper : (A-C limitValue*B).degree < B.degree) (z : ℂ) (regular : B.eval z ≠ 0) :
    A.eval z/B.eval z-limitValue = ∑ α ∈ S, (A.eval α/B.derivative.eval α)/(z-α) := by
  classical
  let R := A-C limitValue*B
  have bval (t : ℂ) : B.eval t = b*(nodal S id).eval t := by rw [factor,eval_mul,eval_C]
  have dval (t : ℂ) : B.derivative.eval t = b*(nodal S id).derivative.eval t := by
    rw [factor,derivative_C_mul,eval_mul,eval_C]
  have rz (α : ℂ) (ha : α ∈ S) : B.eval α=0 := by
    rw [bval,show (nodal S id).eval α=0 from eval_nodal_at_node (v:=id) ha,mul_zero]
  have notroot (α : ℂ) (ha : α ∈ S) : z ≠ id α := fun eq => regular (eq ▸ rz α ha)
  have deg : R.degree < (S.card:WithBot ℕ) := by
    have eq : B.degree=(S.card:WithBot ℕ) := by rw [factor,degree_C_mul hb,degree_nodal]
    exact eq ▸ proper
  have inter := eq_interpolate (f:=R) (v:=id) Function.injective_id.injOn deg
  have val := congrArg (Polynomial.eval z) inter
  rw [eval_interpolate_not_at_node _ notroot] at val
  have term (α : ℂ) (ha : α ∈ S) : nodalWeight S id α*(z-id α)⁻¹*R.eval (id α) =
      b*((A.eval α/B.derivative.eval α)/(z-α)) := by
    rw [nodalWeight_eq_eval_derivative_nodal ha]
    simp only [id_eq,R,eval_sub,eval_mul,eval_C,rz α ha,mul_zero,sub_zero,dval]
    rw [div_mul_eq_div_div]
    field_simp [hb]
  rw [Finset.sum_congr rfl term,←Finset.mul_sum] at val
  simp only [R,eval_sub,eval_mul,eval_C] at val
  apply (sub_eq_iff_eq_add.mpr ((div_eq_iff regular).mpr ?_))
  rw [bval] at val ⊢
  linear_combination val

theorem pole_sum_at_zero (S : Finset ℂ) (A B : ℂ[X]) (b limitValue : ℂ)
    (hb : b ≠ 0) (factor : B=C b * nodal S id)
    (hB : B.eval 0 ≠ 0) (proper : (A-C limitValue*B).degree < B.degree) :
    A.eval 0/B.eval 0-limitValue = -∑ α ∈ S, A.eval α/(α*B.derivative.eval α) := by
  rw [partial_fraction_nonroot S A B b limitValue hb factor proper 0 hB,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro α _
  simp only [zero_sub,div_neg,←div_mul_eq_div_div,mul_comm α]

theorem real_origin_of_real_residues (S : Finset ℂ) (A B : ℂ[X]) (b : ℂ)
    (hb : b ≠ 0) (factor : B=C b * nodal S id) (hB : B.eval 0 ≠ 0)
    (proper : (A-C (conj (A.eval 0/B.eval 0))*B).degree < B.degree)
    (realResidue : ∀ α ∈ S, (A.eval α/(α*B.derivative.eval α)).im=0) :
    (A.eval 0/B.eval 0).im=0 := by
  have eq := pole_sum_at_zero S A B b _ hb factor hB proper
  have im := congrArg Complex.im eq
  simp only [Complex.sub_im,Complex.conj_im,Complex.neg_im,Complex.im_sum] at im
  rw [Finset.sum_eq_zero realResidue] at im
  linarith

end ClosedSimilarity.RationalArclength
#print axioms ClosedSimilarity.RationalArclength.real_origin_of_real_residues
