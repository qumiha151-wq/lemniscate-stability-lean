import Lemniscate.PeriodicMatrixIdentification

/-! Finite cosine polynomials, all their classical derivatives, and their
actual L2 norms. Linearity is checked for the differential expression itself. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleCosinePolynomial (I : Finset ℕ) (v : ℕ → ℂ) (k : ℕ) :
    C(AddCircle T, ℂ) := ∑ j ∈ I, v j • circleCosineJet T j k

theorem circle_cosine_polynomial_deriv (I : Finset ℕ) (v : ℕ → ℂ) (k : ℕ) :
    HasCircleDeriv T (circleCosinePolynomial T I v k) (circleCosinePolynomial T I v (k+1)) := by
  intro x
  simpa only [circleCosinePolynomial, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul] using HasDerivAt.fun_sum (u := I)
      (fun j _ => (circle_cosine_jet_deriv T j k x).const_mul (v j))

theorem circle_continuous_l2_sum (I : Finset ℕ) (f : ℕ → C(AddCircle T, ℂ)) :
    circleContinuousL2 T (∑ j ∈ I, f j) = ∑ j ∈ I, circleContinuousL2 T (f j) :=
  map_sum (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ) f I

theorem circle_cosine_polynomial_l2 (I : Finset ℕ) (v : ℕ → ℂ) :
    circleContinuousL2 T (circleCosinePolynomial T I v 0) =
      ∑ j ∈ I, v j • circleEvenCosineMode T j := by
  simp only [circleCosinePolynomial, circle_continuous_l2_sum,
    circle_continuous_l2_smul, circle_cosine_jet_zero_l2]

theorem circle_cosine_polynomial_norm_sq (I : Finset ℕ) (v : ℕ → ℂ) :
    ‖circleContinuousL2 T (circleCosinePolynomial T I v 0)‖^2 = ∑ j ∈ I, ‖v j‖^2 := by
  rw [circle_cosine_polynomial_l2]
  have hi := (circle_even_cosine_orthonormal T).inner_sum v v I
  have hr := congrArg Complex.re hi
  have hn : (inner ℂ (∑ j ∈ I, v j • circleEvenCosineMode T j)
      (∑ j ∈ I, v j • circleEvenCosineMode T j)).re =
      ‖∑ j ∈ I, v j • circleEvenCosineMode T j‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [hn] at hr
  simpa only [Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, Complex.ofReal_re] using hr

theorem circle_symmetric_expression_add (h h₁ h₂ f f₁ f₂ f₄ g g₁ g₂ g₄ : C(AddCircle T, ℂ)) :
    circleSymmetricExpression T h h₁ h₂ (f+g) (f₁+g₁) (f₂+g₂) (f₄+g₄) =
      circleSymmetricExpression T h h₁ h₂ f f₁ f₂ f₄ +
        circleSymmetricExpression T h h₁ h₂ g g₁ g₂ g₄ := by
  ext x
  simp only [circleSymmetricExpression, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem circle_symmetric_expression_smul (h h₁ h₂ f f₁ f₂ f₄ : C(AddCircle T, ℂ)) (c : ℂ) :
    circleSymmetricExpression T h h₁ h₂ (c • f) (c • f₁) (c • f₂) (c • f₄) =
      c • circleSymmetricExpression T h h₁ h₂ f f₁ f₂ f₄ := by
  ext x
  simp only [circleSymmetricExpression, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem circle_symmetric_expression_sum (h h₁ h₂ : C(AddCircle T, ℂ)) (I : Finset ℕ)
    (f f₁ f₂ f₄ : ℕ → C(AddCircle T, ℂ)) :
    circleSymmetricExpression T h h₁ h₂ (∑ j ∈ I, f j) (∑ j ∈ I, f₁ j)
      (∑ j ∈ I, f₂ j) (∑ j ∈ I, f₄ j) =
        ∑ j ∈ I, circleSymmetricExpression T h h₁ h₂ (f j) (f₁ j) (f₂ j) (f₄ j) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [circleSymmetricExpression]
  | @insert j I hj ih =>
      simp only [Finset.sum_insert hj]
      rw [circle_symmetric_expression_add, ih]

noncomputable def circleSymmetricPolynomial (h h₁ h₂ : C(AddCircle T, ℂ))
    (I : Finset ℕ) (v : ℕ → ℂ) : C(AddCircle T, ℂ) :=
  circleSymmetricExpression T h h₁ h₂ (circleCosinePolynomial T I v 0)
    (circleCosinePolynomial T I v 1) (circleCosinePolynomial T I v 2)
    (circleCosinePolynomial T I v 4)

theorem circle_symmetric_polynomial_sum (h h₁ h₂ : C(AddCircle T, ℂ))
    (I : Finset ℕ) (v : ℕ → ℂ) :
    circleSymmetricPolynomial T h h₁ h₂ I v =
      ∑ j ∈ I, v j • circleSymmetricCosineMode T h h₁ h₂ j := by
  simp only [circleSymmetricPolynomial, circleCosinePolynomial, circle_symmetric_expression_sum,
    circle_symmetric_expression_smul, circleSymmetricCosineMode]

end Lemniscate
