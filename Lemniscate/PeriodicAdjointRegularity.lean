import Lemniscate.PeriodicAdjointFourier
import Lemniscate.PeriodicEllipticBootstrap

/-! Maximal-domain regularity for the actual Hilbert adjoint. The proof first
gains H2 from the distributional equation and then uses weak product rules to
construct the third and fourth derivatives in L2. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_fourierCoeff_add (f g : CircleL2 T) (n : ℤ) :
    fourierCoeff (f+g) n = fourierCoeff f n+fourierCoeff g n := by
  simp only [← fourierBasis_repr, HilbertBasis.repr_apply_apply, inner_add_right]

theorem circle_hilbert_adjoint_mem_h2 (h h₁ h₂ : C(AddCircle T, ℂ))
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (g : (circleH4PMap T h h₁ h₂).adjoint.domain) :
    InCircleH2 T (g : CircleL2 T) := by
  apply circle_h2_of_fourth_distribution T (g : CircleL2 T)
    ((-45/4:ℂ) • circleMultiplyL2 T h g)
    ((75/8:ℂ) • circleMultiplyL2 T h₁ g)
    ((-1/4:ℂ) • (circleH4PMap T h h₁ h₂).adjoint g +
      (-21/2:ℂ) • (g : CircleL2 T) + (15/8:ℂ) • circleMultiplyL2 T h₂ g)
  intro n
  simp only [circle_fourierCoeff_add, circle_fourierCoeff_smul]
  have hk := circle_hilbert_adjoint_fourier T h h₁ h₂ hreal h₁real h₂real g n
  linear_combination (1/4:ℂ)*hk

theorem circle_multiply_first_fourier (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (f f₁ : CircleL2 T) (hf : HasWeakCircleDeriv T f f₁) (n : ℤ) :
    circleFrequencyFactor T n*fourierCoeff (circleMultiplyL2 T h f) n =
      fourierCoeff (circleMultiplyL2 T h f₁) n+
        fourierCoeff (circleMultiplyL2 T h₁ f) n := by
  have hp := fourier_of_weak_circle_deriv T _ _
    (circle_real_multiply_weak_deriv T h h₁ hh hreal h₁real f f₁ hf) n
  simpa only [circle_fourierCoeff_add] using hp.symm

theorem circle_multiply_second_fourier (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (f f₁ f₂ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) (hf₁ : HasWeakCircleDeriv T f₁ f₂) (n : ℤ) :
    (circleFrequencyFactor T n)^2*fourierCoeff (circleMultiplyL2 T h f) n =
      fourierCoeff (circleMultiplyL2 T h f₂) n+
      2*fourierCoeff (circleMultiplyL2 T h₁ f₁) n+
      fourierCoeff (circleMultiplyL2 T h₂ f) n := by
  have hp := circle_real_multiply_weak_deriv T h h₁ hh hreal h₁real f f₁ hf
  have hp₁ := circle_weak_deriv_add T _ _ _ _
    (circle_real_multiply_weak_deriv T h h₁ hh hreal h₁real f₁ f₂ hf₁)
    (circle_real_multiply_weak_deriv T h₁ h₂ hh₁ h₁real h₂real f f₁ hf)
  have hn := fourier_of_weak_circle_deriv T _ _ hp₁ n
  rw [fourier_of_weak_circle_deriv T _ _ hp n] at hn
  simp only [circle_fourierCoeff_add] at hn
  linear_combination -hn

theorem circle_hilbert_adjoint_mem_h4 (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (g : (circleH4PMap T h h₁ h₂).adjoint.domain) :
    InCircleH4 T (g : CircleL2 T) := by
  obtain ⟨g₁, g₂, hg, hg₁⟩ :=
    circle_hilbert_adjoint_mem_h2 T h h₁ h₂ hreal h₁real h₂real g
  let g₄ : CircleL2 T := (-1/4:ℂ) •
    ((circleH4PMap T h h₁ h₂).adjoint g +
      (45:ℂ) • circleMultiplyL2 T h g₂ +
      (105/2:ℂ) • circleMultiplyL2 T h₁ g₁ + (42:ℂ) • (g : CircleL2 T))
  have hg₂ : HasWeakCircleSecond T g₂ g₄ := by
    apply weak_circle_second_of_fourier
    intro n
    rw [← circle_frequency_factor_sq, fourier_of_weak_circle_deriv T _ _ hg₁,
      fourier_of_weak_circle_deriv T _ _ hg]
    dsimp only [g₄]
    simp only [circle_fourierCoeff_smul, circle_fourierCoeff_add]
    have hk := circle_hilbert_adjoint_fourier T h h₁ h₂ hreal h₁real h₂real g n
    have hp₂ := circle_multiply_second_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real
      (g : CircleL2 T) g₁ g₂ hg hg₁ n
    have hp₁ := circle_multiply_first_fourier T h₁ h₂ hh₁ h₁real h₂real
      (g : CircleL2 T) g₁ hg n
    linear_combination (-1/4:ℂ)*hk + (45/4:ℂ)*hp₂ - (75/8:ℂ)*hp₁
  obtain ⟨g₃, hg₂', hg₃⟩ := (weak_circle_second_iff_deriv_chain T g₂ g₄).mp hg₂
  exact ⟨g₁, g₂, g₃, g₄, hg, hg₁, hg₂', hg₃⟩

theorem circle_hilbert_adjoint_domain (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) :
    (circleH4PMap T h h₁ h₂).adjoint.domain = circleH4Domain T := by
  apply le_antisymm
  · intro g hg
    exact circle_hilbert_adjoint_mem_h4 T h h₁ h₂ hh hh₁ hreal h₁real h₂real ⟨g, hg⟩
  · exact (circle_h4_formal_le_hilbert_adjoint T h h₁ h₂ hh hh₁ hreal h₁real h₂real).1

theorem circle_hilbert_adjoint_eq_formal (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) :
    (circleH4PMap T h h₁ h₂).adjoint = circleH4FormalAdjointPMap T h h₁ := by
  apply LinearPMap.ext
    (circle_hilbert_adjoint_domain T h h₁ h₂ hh hh₁ hreal h₁real h₂real)
  intro g hg hg'
  exact circle_h4_hilbert_adjoint_value T h h₁ h₂ hh hh₁ hreal h₁real h₂real ⟨g, hg'⟩ hg

theorem circle_h4_formal_adjoint_closed (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) :
    (circleH4FormalAdjointPMap T h h₁).IsClosed := by
  rw [← circle_hilbert_adjoint_eq_formal T h h₁ h₂ hh hh₁ hreal h₁real h₂real]
  exact circle_h4_hilbert_adjoint_closed T h h₁ h₂

end Lemniscate
