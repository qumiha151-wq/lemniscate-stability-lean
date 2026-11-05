import Lemniscate.ShortHeadSymmetric

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0<T)]

theorem circle_short_symmetric_conj (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x,conj (h x)=h x) (h₁real : ∀ x,conj (h₁ x)=h₁ x)
    (h₂real : ∀ x,conj (h₂ x)=h₂ x)
    (j : Fin 5) (f g : circleH4Domain T) :
    conj (circleShortSymmetricCoefficient T h h₁ h₂ j g f)=
      circleShortSymmetricCoefficient T h h₁ h₂ j f g := by
  by_cases hj : j=0
  · subst j
    rw [circle_short_zero_symmetric T h h₁ h₂ hh hh₁ hreal h₁real h₂real,
      circle_short_zero_symmetric T h h₁ h₂ hh hh₁ hreal h₁real h₂real]
    simp only [map_mul,map_add,map_div₀,map_one,map_ofNat,inner_conj_symm]
    ring
  · simp only [circleShortSymmetricCoefficient,if_neg hj,map_mul,map_add,
      map_div₀,map_one,map_ofNat,inner_conj_symm]
    ring

theorem circle_reduced_shifted_conj
    (H : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (hH : ∀ j f g,conj (H j g f)=H j f g) (k : Fin 5) (f g : circleH4Domain T) :
    conj (circleReducedShiftedCoefficient T H k g f)=
      circleReducedShiftedCoefficient T H k f g := by
  fin_cases k <;>
    simp only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
      map_mul,map_add,map_div₀,map_one,map_ofNat,Complex.conj_ofReal,inner_conj_symm,hH] <;> ring

theorem circle_short_bernstein_conj (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x,conj (h x)=h x) (h₁real : ∀ x,conj (h₁ x)=h₁ x)
    (h₂real : ∀ x,conj (h₂ x)=h₂ x)
    (j : Fin 5) (f g : circleH4Domain T) :
    conj (circleShortBernsteinPairing T h h₁ h₂ j g f)=
      circleShortBernsteinPairing T h h₁ h₂ j f g := by
  simp only [circleShortBernsteinPairing,circleShiftedBernsteinPairing,map_sum,map_mul,
    map_ratCast,circle_reduced_shifted_conj T _
      (circle_short_symmetric_conj T h h₁ h₂ hh hh₁ hreal h₁real h₂real)]

end Lemniscate
