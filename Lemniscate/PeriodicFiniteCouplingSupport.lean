import Lemniscate.PeriodicFiniteCouplingTest
import Lemniscate.PeriodicFiniteCoordinates

/-! The cubic Bloch coefficient has no high-frequency output on the finite
test functions. Thus the low-high reduced pairing only has degree two. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

private theorem finite_phase_fourier_zero (n : ℤ) (hn : 32 ≤ |(n:ℝ)|) :
    fourierCoeff (circleFiniteRotationPhase T:CircleL2 T) n = 0 ∧
    fourierCoeff (circleFiniteAdjointPhase T) n = 0 ∧
    fourierCoeff (circleHouseholderAnchor T) n = 0 := by
  have hout (i : Fin 31) : n ≠ evenHeadFrequency i := by
    intro hi
    exact not_lt_of_ge hn ((even_head_frequency_range n).mp ⟨i, hi.symm⟩).2
  have hh (v : Fin 31 → ℂ) := circle_even_head_fourier_outside T v n hout
  refine ⟨?_, ?_, ?_⟩
  · rw [circle_finite_rotation_phase_head]
    exact hh _
  · rw [circle_finite_adjoint_phase_head]
    exact hh _
  · rw [circle_householder_anchor_fourier, if_neg (by
      intro h; subst n; norm_num at hn), if_neg (by
      intro h; subst n; norm_num at hn)]
    simp only [sub_self, mul_zero]

private theorem finite_right_fourier_zero (f : circleH4Domain T) (n : ℤ)
    (he : fourierCoeff (circleFiniteRotationPhase T:CircleL2 T) n = 0)
    (ha : fourierCoeff (circleHouseholderAnchor T) n = 0)
    (hf : fourierCoeff (f:CircleL2 T) n = 0) :
    fourierCoeff (circleFiniteRightInput T f:CircleL2 T) n = 0 := by
  simp only [circleFiniteRightInput, neutralTransformInvDomain, neutralHouseholderDomain,
    Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul_of_tower,
    circle_householder_anchor_h4_coe, circle_fourierCoeff_sub, circle_fourierCoeff_smul,
    circle_fourierCoeff_add, he, ha, hf, add_zero, mul_zero, sub_zero]

private theorem finite_left_adjoint_fourier_zero (f : circleH4Domain T) (n : ℤ)
    (he : fourierCoeff (circleFiniteRotationPhase T:CircleL2 T) n = 0)
    (hp : fourierCoeff (circleFiniteAdjointPhase T) n = 0)
    (ha : fourierCoeff (circleHouseholderAnchor T) n = 0)
    (hf : fourierCoeff (f:CircleL2 T) n = 0) :
    fourierCoeff (circleFiniteLeftAdjointDomain T f:CircleL2 T) n = 0 := by
  let u := neutralHouseholderAdjointDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f
  have hu : fourierCoeff (u:CircleL2 T) n = 0 := by
    change fourierCoeff ((f:CircleL2 T)-
      (conj (1+inner ℂ (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T))⁻¹*
        inner ℂ ((circleFiniteRotationPhase T:CircleL2 T)+circleHouseholderAnchor T) (f:CircleL2 T)) •
        ((circleFiniteRotationPhase T:CircleL2 T)+circleHouseholderAnchor T)) n = 0
    simp only [circle_fourierCoeff_sub, circle_fourierCoeff_smul, circle_fourierCoeff_add,
      he, ha, hf, add_zero, mul_zero, sub_zero]
  change fourierCoeff ((u:CircleL2 T)+inner ℂ (circleFiniteRotationPhase T:CircleL2 T) (u:CircleL2 T) •
    ((circleFiniteAdjointPhaseH4 T:CircleL2 T)-(circleFiniteRotationPhase T:CircleL2 T))) n = 0
  simp only [circle_fourierCoeff_add, circle_fourierCoeff_smul, circle_fourierCoeff_sub,
    circle_finite_adjoint_phase_h4_coe, hu, hp, he, sub_self, mul_zero, add_zero]

theorem circle_finite_third_test_fourier_zero (h h₁ h₂ : C(AddCircle T, ℂ))
    (v : Fin 31 → ℂ) (n : ℤ) (hn : 32 ≤ |(n:ℝ)|) :
    fourierCoeff (circleFiniteCoefficientTest T h h₁ h₂ 3 (circleEvenHeadH4 T v)) n = 0 := by
  rcases finite_phase_fourier_zero T n hn with ⟨he, hp, ha⟩
  have hf : fourierCoeff (circleEvenHeadH4 T v:CircleL2 T) n = 0 := by
    apply circle_even_head_fourier_outside
    intro i hi
    exact not_lt_of_ge hn ((even_head_frequency_range n).mp ⟨i, hi.symm⟩).2
  have hL := finite_left_adjoint_fourier_zero T _ n he hp ha hf
  have hR := finite_right_fourier_zero T _ n he ha hf
  have hA (u : circleH4Domain T) (hu : fourierCoeff (u:CircleL2 T) n = 0) :
      fourierCoeff (circleBlochCoefficient T h h₁ h₂ 3 u) n = 0 := by
    rw [circle_bloch_coefficient_three_apply, circle_fourierCoeff_smul, circle_fourierCoeff_smul,
      fourier_of_weak_circle_deriv T _ _ (circleH4Jet T u).hfirst, hu]
    simp only [mul_zero]
  change fourierCoeff ((1/2:ℂ) •
    (circleBlochCoefficient T h h₁ h₂ 3 (circleFiniteLeftAdjointDomain T (circleEvenHeadH4 T v))+
      circleBlochCoefficient T h h₁ h₂ 3 (circleFiniteRightInput T (circleEvenHeadH4 T v)))) n = 0
  rw [circle_fourierCoeff_smul, circle_fourierCoeff_add, hA _ hL, hA _ hR]
  simp only [add_zero, mul_zero]

end Lemniscate
