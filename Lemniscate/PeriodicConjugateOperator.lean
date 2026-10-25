import Lemniscate.PeriodicConjugation

/-! Pointwise complex conjugation preserves the actual H4 domain and commutes
with the differential operator for real coefficient functions. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_conjugate_mem_h4 (f : circleH4Domain T) :
    InCircleH4 T (circleConjugate T (f : CircleL2 T)) := by
  apply circle_h4_of_fourth_fourier T _ (circleConjugate T (circleH4Jet T f).fourth)
  intro n
  rw [circle_conjugate_fourier, circle_h4_fourth_fourier, map_mul, map_pow,
    circle_frequency_factor_conjugate_neg, circle_conjugate_fourier]

noncomputable def circleConjugateH4 (f : circleH4Domain T) : circleH4Domain T :=
  ⟨circleConjugate T (f : CircleL2 T), circle_conjugate_mem_h4 T f⟩

theorem circle_conjugate_h4_coe (f : circleH4Domain T) :
    (circleConjugateH4 T f : CircleL2 T) = circleConjugate T (f : CircleL2 T) := rfl

theorem circle_conjugate_h4_first (f : circleH4Domain T) :
    (circleH4Jet T (circleConjugateH4 T f)).first =
      circleConjugate T (circleH4Jet T f).first :=
  weak_circle_deriv_unique T _ _ _ (circleH4Jet T (circleConjugateH4 T f)).hfirst
    (circle_conjugate_weak_deriv T _ _ (circleH4Jet T f).hfirst)

theorem circle_conjugate_h4_second (f : circleH4Domain T) :
    (circleH4Jet T (circleConjugateH4 T f)).second =
      circleConjugate T (circleH4Jet T f).second := by
  apply weak_circle_deriv_unique T _ _ _ (circleH4Jet T (circleConjugateH4 T f)).hsecond
  rw [circle_conjugate_h4_first]
  exact circle_conjugate_weak_deriv T _ _ (circleH4Jet T f).hsecond

theorem circle_conjugate_h4_fourth (f : circleH4Domain T) :
    (circleH4Jet T (circleConjugateH4 T f)).fourth =
      circleConjugate T (circleH4Jet T f).fourth := by
  apply circle_fourier_ext T
  intro n
  rw [circle_h4_fourth_fourier, circle_conjugate_fourier, circle_h4_fourth_fourier,
    map_mul, map_pow, circle_frequency_factor_conjugate_neg]
  change (circleFrequencyFactor T n)^4 *
    fourierCoeff (circleConjugate T (f : CircleL2 T)) n = _
  rw [circle_conjugate_fourier]

theorem circle_h4_operator_conjugate (h h₁ h₂ : C(AddCircle T, ℂ))
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (f : circleH4Domain T) :
    circleH4Operator T h h₁ h₂ (circleConjugateH4 T f) =
      circleConjugate T (circleH4Operator T h h₁ h₂ f) := by
  simp only [circle_h4_operator_apply, circleLinearL2Expression, circleSymmetricL2Expression,
    circle_conjugate_add, circle_conjugate_sub, circle_conjugate_smul,
    circle_conjugate_h4_coe, circle_conjugate_h4_first, circle_conjugate_h4_second,
    circle_conjugate_h4_fourth, circle_conjugate_multiply T h hreal,
    circle_conjugate_multiply T h₁ h₁real, circle_conjugate_multiply T h₂ h₂real,
    map_neg, map_div₀, map_ofNat, map_one]

theorem circle_adjoint_pairing_real (h h₁ h₂ : C(AddCircle T, ℂ))
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (e ψ : CircleL2 T)
    (he : circleConjugate T e = e)
    (hψ : inner ℂ ψ e = 1 ∧ ∀ f : circleH4Domain T,
      inner ℂ ψ (circleH4Operator T h h₁ h₂ f) = 0)
    (huniq : ∀ ψ' : CircleL2 T, (inner ℂ ψ' e = 1 ∧ ∀ f : circleH4Domain T,
      inner ℂ ψ' (circleH4Operator T h h₁ h₂ f) = 0) → ψ' = ψ) :
    circleConjugate T ψ = ψ := by
  apply huniq
  constructor
  · calc
      inner ℂ (circleConjugate T ψ) e =
          inner ℂ (circleConjugate T ψ) (circleConjugate T e) := by rw [he]
      _ = conj (inner ℂ ψ e) := circle_conjugate_inner T ψ e
      _ = 1 := by rw [hψ.1, map_one]
  · intro f
    calc
      inner ℂ (circleConjugate T ψ) (circleH4Operator T h h₁ h₂ f) =
          inner ℂ (circleConjugate T ψ)
            (circleConjugate T (circleH4Operator T h h₁ h₂ (circleConjugateH4 T f))) := by
        rw [circle_h4_operator_conjugate T h h₁ h₂ hreal h₁real h₂real,
          circle_conjugate_involutive]
      _ = conj (inner ℂ ψ (circleH4Operator T h h₁ h₂ (circleConjugateH4 T f))) :=
        circle_conjugate_inner T ψ _
      _ = 0 := by rw [hψ.2, map_zero]

end Lemniscate
