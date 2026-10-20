import Lemniscate.PeriodicAdjointRegularity

/-! Apply the same maximal-domain argument in the reverse direction. This
identifies the adjoint of the formal adjoint with the original H4 operator,
and proves closedness on its stated domain, not merely closability. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_formal_adjoint_adjoint_fourier (h h₁ : C(AddCircle T, ℂ))
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (g : (circleH4FormalAdjointPMap T h h₁).adjoint.domain) (n : ℤ) :
    fourierCoeff ((circleH4FormalAdjointPMap T h h₁).adjoint g) n =
      -4*(circleFrequencyFactor T n)^4*fourierCoeff (g : CircleL2 T) n -
      45*(circleFrequencyFactor T n)^2*fourierCoeff (circleMultiplyL2 T h g) n +
      (105/2)*circleFrequencyFactor T n*fourierCoeff (circleMultiplyL2 T h₁ g) n -
      42*fourierCoeff (g : CircleL2 T) n := by
  have hd : Dense ((circleH4FormalAdjointPMap T h h₁).domain : Set (CircleL2 T)) :=
    circle_h4_domain_dense T
  have hi := (LinearPMap.adjoint_isFormalAdjoint hd).symm
    ⟨fourierBasis (T := T) n, circle_fourier_mem_h4 T n⟩ g
  change inner ℂ
    ((-4:ℂ) • (circleH4Jet T ⟨_, circle_fourier_mem_h4 T n⟩).fourth -
      (45:ℂ) • circleMultiplyL2 T h (circleH4Jet T ⟨_, circle_fourier_mem_h4 T n⟩).second -
      (105/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T ⟨_, circle_fourier_mem_h4 T n⟩).first -
      (42:ℂ) • fourierBasis (T := T) n) (g : CircleL2 T) =
      inner ℂ (fourierBasis (T := T) n) ((circleH4FormalAdjointPMap T h h₁).adjoint g) at hi
  rw [circle_fourier_h4_jet] at hi
  simp only [circleFourierH4Jet, inner_sub_left, inner_smul_left,
    circle_multiply_l2_symmetric T h hreal,
    circle_multiply_l2_symmetric T h₁ h₁real, inner_smul_left,
    map_pow, circle_frequency_factor_conj, ← HilbertBasis.repr_apply_apply,
    fourierBasis_repr] at hi
  norm_num [map_ofNat] at hi
  linear_combination -hi

theorem circle_formal_adjoint_adjoint_mem_h2 (h h₁ : C(AddCircle T, ℂ))
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (g : (circleH4FormalAdjointPMap T h h₁).adjoint.domain) :
    InCircleH2 T (g : CircleL2 T) := by
  apply circle_h2_of_fourth_distribution T (g : CircleL2 T)
    ((-45/4:ℂ) • circleMultiplyL2 T h g)
    ((105/8:ℂ) • circleMultiplyL2 T h₁ g)
    ((-1/4:ℂ) • (circleH4FormalAdjointPMap T h h₁).adjoint g +
      (-21/2:ℂ) • (g : CircleL2 T))
  intro n
  simp only [circle_fourierCoeff_add, circle_fourierCoeff_smul]
  have hk := circle_formal_adjoint_adjoint_fourier T h h₁ hreal h₁real g n
  linear_combination (1/4:ℂ)*hk

theorem circle_formal_adjoint_adjoint_mem_h4 (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (g : (circleH4FormalAdjointPMap T h h₁).adjoint.domain) :
    InCircleH4 T (g : CircleL2 T) := by
  obtain ⟨g₁, g₂, hg, hg₁⟩ :=
    circle_formal_adjoint_adjoint_mem_h2 T h h₁ hreal h₁real g
  let g₄ : CircleL2 T := (-1/4:ℂ) •
    ((circleH4FormalAdjointPMap T h h₁).adjoint g +
      (45:ℂ) • circleMultiplyL2 T h g₂ +
      (75/2:ℂ) • circleMultiplyL2 T h₁ g₁ + (42:ℂ) • (g : CircleL2 T) +
      (-15/2:ℂ) • circleMultiplyL2 T h₂ g)
  have hg₂ : HasWeakCircleSecond T g₂ g₄ := by
    apply weak_circle_second_of_fourier
    intro n
    rw [← circle_frequency_factor_sq, fourier_of_weak_circle_deriv T _ _ hg₁,
      fourier_of_weak_circle_deriv T _ _ hg]
    dsimp only [g₄]
    simp only [circle_fourierCoeff_smul, circle_fourierCoeff_add]
    have hk := circle_formal_adjoint_adjoint_fourier T h h₁ hreal h₁real g n
    have hp₂ := circle_multiply_second_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real
      (g : CircleL2 T) g₁ g₂ hg hg₁ n
    have hp₁ := circle_multiply_first_fourier T h₁ h₂ hh₁ h₁real h₂real
      (g : CircleL2 T) g₁ hg n
    linear_combination (-1/4:ℂ)*hk + (45/4:ℂ)*hp₂ - (105/8:ℂ)*hp₁
  obtain ⟨g₃, hg₂', hg₃⟩ := (weak_circle_second_iff_deriv_chain T g₂ g₄).mp hg₂
  exact ⟨g₁, g₂, g₃, g₄, hg, hg₁, hg₂', hg₃⟩

theorem circle_formal_adjoint_adjoint_eq (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) :
    (circleH4FormalAdjointPMap T h h₁).adjoint = circleH4PMap T h h₁ h₂ := by
  have hd : Dense ((circleH4FormalAdjointPMap T h h₁).domain : Set (CircleL2 T)) :=
    circle_h4_domain_dense T
  have hi := circle_h4_pmap_formal_adjoint T h h₁ h₂ hh hh₁ hreal h₁real h₂real
  apply LinearPMap.ext
  · apply le_antisymm
    · intro g hg
      exact circle_formal_adjoint_adjoint_mem_h4 T h h₁ h₂ hh hh₁ hreal h₁real h₂real ⟨g, hg⟩
    · exact (LinearPMap.IsFormalAdjoint.le_adjoint hd hi.symm).1
  · intro g hg hg'
    apply LinearPMap.adjoint_apply_eq hd
    intro f
    exact hi ⟨g, hg'⟩ f

theorem circle_h4_pmap_closed (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) :
    (circleH4PMap T h h₁ h₂).IsClosed := by
  rw [← circle_formal_adjoint_adjoint_eq T h h₁ h₂ hh hh₁ hreal h₁real h₂real]
  exact LinearPMap.adjoint_isClosed (circle_h4_domain_dense T)

end Lemniscate
