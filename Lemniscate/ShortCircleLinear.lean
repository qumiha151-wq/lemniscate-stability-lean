import Lemniscate.ShortCircleForms
import Lemniscate.PeriodicCenteredBlochLinear

namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0<T)]

noncomputable def circleShortTransformedLinear (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  (circleShortHouseholder T).toLinearMap.comp
    ((neutralTransform (circleShortRotationApproximation T)
      (circleShortAdjointApproximation T:CircleL2 T)).toLinearMap.comp
        ((circleBlochCoefficient T h h₁ h₂ j).comp
          ((neutralInverseDomainLinear (circleShortRotationApproximation T)
            (circleShortAdjointApproximation T:CircleL2 T)).comp
            (householderDomainLinear (circleShortRotationApproximation T)
              (circleHouseholderAnchorH4 T)))))

theorem circle_short_transformed_linear_apply (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f : circleH4Domain T) :
    circleShortTransformedLinear T h h₁ h₂ j f=
      circleShortTransformedCoefficient T h h₁ h₂ j f := rfl

theorem circle_short_householder_linear_apply (f : circleH4Domain T) :
    householderDomainLinear (circleShortRotationApproximation T)
      (circleHouseholderAnchorH4 T) f=circleShortHouseholderH4 T f := rfl

theorem circle_short_symmetric_sum_left {ι : Type*} (I : Finset ι)
    (h h₁ h₂ : C(AddCircle T, ℂ)) (j : Fin 5)
    (f : ι → circleH4Domain T) (g : circleH4Domain T) :
    circleShortSymmetricCoefficient T h h₁ h₂ j (∑ i∈I,f i) g=
      ∑ i∈I,circleShortSymmetricCoefficient T h h₁ h₂ j (f i) g := by
  simp only [circleShortSymmetricCoefficient,← circle_short_transformed_linear_apply,
    ← circle_short_householder_linear_apply]
  split_ifs <;>
    simp only [map_sum,Submodule.coe_sum,sum_inner,mul_add,Finset.mul_sum,Finset.sum_add_distrib]

theorem circle_short_symmetric_sum_right {ι : Type*} (I : Finset ι)
    (h h₁ h₂ : C(AddCircle T, ℂ)) (j : Fin 5)
    (f : circleH4Domain T) (g : ι → circleH4Domain T) :
    circleShortSymmetricCoefficient T h h₁ h₂ j f (∑ i∈I,g i)=
      ∑ i∈I,circleShortSymmetricCoefficient T h h₁ h₂ j f (g i) := by
  simp only [circleShortSymmetricCoefficient,← circle_short_transformed_linear_apply,
    ← circle_short_householder_linear_apply]
  split_ifs <;>
    simp only [map_sum,Submodule.coe_sum,inner_sum,mul_add,Finset.mul_sum,Finset.sum_add_distrib]

theorem circle_short_symmetric_smul_left (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (c : ℂ) (f g : circleH4Domain T) :
    circleShortSymmetricCoefficient T h h₁ h₂ j (c • f) g=
      conj c*circleShortSymmetricCoefficient T h h₁ h₂ j f g := by
  simp only [circleShortSymmetricCoefficient,← circle_short_transformed_linear_apply,
    ← circle_short_householder_linear_apply]
  split_ifs <;>
    simp only [map_smul,Submodule.coe_smul_of_tower,inner_smul_left] <;> ring

theorem circle_short_symmetric_smul_right (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (c : ℂ) (f g : circleH4Domain T) :
    circleShortSymmetricCoefficient T h h₁ h₂ j f (c • g)=
      c*circleShortSymmetricCoefficient T h h₁ h₂ j f g := by
  simp only [circleShortSymmetricCoefficient,← circle_short_transformed_linear_apply,
    ← circle_short_householder_linear_apply]
  split_ifs <;>
    simp only [map_smul,Submodule.coe_smul_of_tower,inner_smul_right] <;> ring

theorem circle_short_symmetric_zero_left (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (g : circleH4Domain T) :
    circleShortSymmetricCoefficient T h h₁ h₂ j 0 g=0 := by
  simpa only [zero_smul,map_zero,zero_mul] using
    circle_short_symmetric_smul_left T h h₁ h₂ j 0 0 g

theorem circle_short_symmetric_zero_right (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f : circleH4Domain T) :
    circleShortSymmetricCoefficient T h h₁ h₂ j f 0=0 := by
  simpa only [zero_smul,zero_mul] using
    circle_short_symmetric_smul_right T h h₁ h₂ j 0 f 0

end Lemniscate
