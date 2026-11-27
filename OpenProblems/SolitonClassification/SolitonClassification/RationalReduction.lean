import SolitonClassification.RationalPoleCoefficient
import Mathlib.RingTheory.EuclideanDomain

noncomputable section
open Polynomial
open scoped Polynomial
namespace ClosedSimilarity.RationalCurvature

/-- Cancellation preserves all originally regular evaluations and makes
the new numerator and denominator coprime. -/
theorem exists_reduced_quotient {A B : ℂ[X]} (bn : B≠0) :
    ∃ U V : ℂ[X], V≠0 ∧ IsCoprime U V ∧
      ∀ z, B.eval z≠0 → V.eval z≠0 ∧ quotient U V z=quotient A B z := by
  classical
  let _ : GCDMonoid ℂ[X] := EuclideanDomain.gcdMonoid _
  let G := GCDMonoid.gcd A B
  let U := A/G
  let V := B/G
  have gn : G≠0 := gcd_ne_zero_of_right bn
  have fa : G*U=A := EuclideanDomain.mul_div_cancel' gn (GCDMonoid.gcd_dvd_left _ _)
  have fb : G*V=B := EuclideanDomain.mul_div_cancel' gn (GCDMonoid.gcd_dvd_right _ _)
  refine ⟨U,V,right_div_gcd_ne_zero bn,isCoprime_div_gcd_div_gcd bn,?_⟩
  intro z b
  have ea := congrArg (Polynomial.eval z) fa
  have eb := congrArg (Polynomial.eval z) fb
  simp only [eval_mul] at ea eb
  have safe : G.eval z≠0 ∧ V.eval z≠0 := mul_ne_zero_iff.mp (eb ▸ b)
  refine ⟨safe.2,?_⟩
  simp only [quotient,←ea,←eb]
  field_simp [safe.1,safe.2]

end ClosedSimilarity.RationalCurvature
