import Lemniscate.PeriodicHilbertAdjoint

/-! Test the genuine Hilbert adjoint on every Fourier mode. This derives its
distributional equation without assuming that its argument lies in H4. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_fourier_power_weak_deriv (n : ℤ) (j : ℕ) :
    HasWeakCircleDeriv T
      ((circleFrequencyFactor T n)^j • fourierBasis (T := T) n)
      ((circleFrequencyFactor T n)^(j+1) • fourierBasis (T := T) n) := by
  have h := circle_classical_weak_deriv T _ _ (circle_fourier_derivative_power T n j)
  simpa only [circle_continuous_l2_smul, circle_continuous_l2_fourier_basis] using h

noncomputable def circleFourierH4Jet (n : ℤ) :
    CircleH4Jet T (fourierBasis (T := T) n) where
  first := circleFrequencyFactor T n • fourierBasis (T := T) n
  second := (circleFrequencyFactor T n)^2 • fourierBasis (T := T) n
  third := (circleFrequencyFactor T n)^3 • fourierBasis (T := T) n
  fourth := (circleFrequencyFactor T n)^4 • fourierBasis (T := T) n
  hfirst := by simpa only [Nat.zero_add, pow_zero, one_smul, pow_one] using
    circle_fourier_power_weak_deriv T n 0
  hsecond := by simpa only [pow_one] using circle_fourier_power_weak_deriv T n 1
  hthird := circle_fourier_power_weak_deriv T n 2
  hfourth := circle_fourier_power_weak_deriv T n 3

theorem circle_fourier_h4_jet (n : ℤ) :
    circleH4Jet T ⟨fourierBasis (T := T) n, circle_fourier_mem_h4 T n⟩ =
      circleFourierH4Jet T n := circle_h4_jet_unique T _ _ _

theorem circle_h4_operator_expanded (h h₁ h₂ : C(AddCircle T, ℂ))
    (f : circleH4Domain T) :
    circleH4Operator T h h₁ h₂ f =
      (-4:ℂ) • (circleH4Jet T f).fourth -
      (45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second -
      (75/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T f).first -
      (42:ℂ) • (f : CircleL2 T) + (15/2:ℂ) • circleMultiplyL2 T h₂ (f : CircleL2 T) := by
  rw [circle_h4_operator_apply]
  unfold circleLinearL2Expression circleSymmetricL2Expression
  module

theorem circle_hilbert_adjoint_fourier (h h₁ h₂ : C(AddCircle T, ℂ))
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (g : (circleH4PMap T h h₁ h₂).adjoint.domain) (n : ℤ) :
    fourierCoeff ((circleH4PMap T h h₁ h₂).adjoint g) n =
      -4*(circleFrequencyFactor T n)^4*fourierCoeff (g : CircleL2 T) n -
      45*(circleFrequencyFactor T n)^2*fourierCoeff (circleMultiplyL2 T h g) n +
      (75/2)*(circleFrequencyFactor T n)*fourierCoeff (circleMultiplyL2 T h₁ g) n -
      42*fourierCoeff (g : CircleL2 T) n +
      (15/2)*fourierCoeff (circleMultiplyL2 T h₂ g) n := by
  have hi := (LinearPMap.adjoint_isFormalAdjoint
    (circle_h4_pmap_dense T h h₁ h₂)).symm
      ⟨fourierBasis (T := T) n, circle_fourier_mem_h4 T n⟩ g
  change inner ℂ (circleH4Operator T h h₁ h₂
    ⟨fourierBasis (T := T) n, circle_fourier_mem_h4 T n⟩) (g : CircleL2 T) =
    inner ℂ (fourierBasis (T := T) n) ((circleH4PMap T h h₁ h₂).adjoint g) at hi
  rw [circle_h4_operator_expanded, circle_fourier_h4_jet] at hi
  simp only [circleFourierH4Jet, inner_add_left, inner_sub_left, inner_smul_left,
    circle_multiply_l2_symmetric T h hreal,
    circle_multiply_l2_symmetric T h₁ h₁real,
    circle_multiply_l2_symmetric T h₂ h₂real, inner_smul_left,
    map_pow, circle_frequency_factor_conj, ← HilbertBasis.repr_apply_apply,
    fourierBasis_repr] at hi
  norm_num [map_ofNat] at hi
  linear_combination -hi

end Lemniscate
