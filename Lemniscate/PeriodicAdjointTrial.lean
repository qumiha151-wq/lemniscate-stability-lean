import Lemniscate.PeriodicBlochFourier
import Lemniscate.PeriodicAdjointSobolevError

/-! Exact adjoint residuals of finite Fourier trial functions. Green's identity
identifies every coefficient, and Parseval includes the complete infinite tail. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_adjoint_polynomial_fourier (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (I : Finset ℤ) (v : ℤ → ℂ) (n : ℤ) :
    fourierCoeff (circleH4FormalAdjoint T h h₁
      (∑ m ∈ I, v m • circleFourierH4 T m)) n =
      ∑ m ∈ I, v m * conj (circleBlochFourierEntry T h 0 m n) := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  have hg := circle_h4_formal_adjoint_green T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    (circleFourierH4 T n) (circleFourierH4 T m)
  change inner ℂ (circleH4Operator T h h₁ h₂ (circleFourierH4 T n))
    (fourierBasis (T := T) m) =
    inner ℂ (fourierBasis (T := T) n)
      (circleH4FormalAdjoint T h h₁ (circleFourierH4 T m)) at hg
  rw [← hg, ← inner_conj_symm, ← circle_bloch_at_zero T h h₁ h₂,
    circle_bloch_basis_pairing T h h₁ h₂ hh hh₁]

theorem circle_adjoint_polynomial_norm_sq (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (I : Finset ℤ) (v : ℤ → ℂ) :
    ‖circleH4FormalAdjoint T h h₁ (∑ m ∈ I, v m • circleFourierH4 T m)‖^2 =
      ∑' n : ℤ, ‖∑ m ∈ I, v m * conj (circleBlochFourierEntry T h 0 m n)‖^2 := by
  rw [circle_norm_sq_fourier]
  congr 1
  funext n
  rw [circle_adjoint_polynomial_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real]

noncomputable def circleNormalizedTrial (e : CircleL2 T) (f : circleH4Domain T) :
    circleH4Domain T := (conj (inner ℂ (f : CircleL2 T) e))⁻¹ • f

theorem circle_normalized_trial_pairing (e : CircleL2 T) (f : circleH4Domain T)
    (hne : inner ℂ (f : CircleL2 T) e ≠ 0) :
    inner ℂ (circleNormalizedTrial T e f : CircleL2 T) e = 1 := by
  change inner ℂ ((conj (inner ℂ (f : CircleL2 T) e))⁻¹ • (f : CircleL2 T)) e = 1
  rw [inner_smul_left, map_inv₀, starRingEnd_self_apply, inv_mul_cancel₀ hne]

theorem circle_normalized_trial_adjoint_norm (h h₁ : C(AddCircle T, ℂ))
    (e : CircleL2 T) (f : circleH4Domain T) :
    ‖circleH4FormalAdjoint T h h₁ (circleNormalizedTrial T e f)‖ =
      ‖circleH4FormalAdjoint T h h₁ f‖ / ‖inner ℂ (f : CircleL2 T) e‖ := by
  rw [circleNormalizedTrial, map_smul, norm_smul, norm_inv, norm_conj]
  ring

end Lemniscate
