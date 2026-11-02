import Lemniscate.PeriodicBlochCenterPolynomial

/-! Linear maps for the actual centered coefficients and the elementary
sesquilinear identities needed for the reduced-energy congruence. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

private noncomputable def householderDomainLinear {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {D : Submodule ℂ E} (e a : D) : D →ₗ[ℂ] D where
  toFun := neutralHouseholderDomain e a
  map_add' f g := by
    apply Subtype.ext
    simp only [neutral_householder_domain_coe,Submodule.coe_add,map_add]
  map_smul' c f := by
    change _ = c • _
    apply Subtype.ext
    simp only [neutral_householder_domain_coe,Submodule.coe_smul_of_tower,map_smul]

private noncomputable def neutralInverseDomainLinear {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {D : Submodule ℂ E} (e : D) (ψ : E) : D →ₗ[ℂ] D where
  toFun := neutralTransformInvDomain e ψ
  map_add' f g := by
    apply Subtype.ext
    simp only [neutral_transform_inv_domain_coe,Submodule.coe_add,map_add]
  map_smul' c f := by
    change _ = c • _
    apply Subtype.ext
    simp only [neutral_transform_inv_domain_coe,Submodule.coe_smul_of_tower,map_smul]

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleCenteredCoefficientLinear (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : CircleL2 T) (j : Fin 5) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  (circleRotationHouseholder T q p).toLinearMap.comp
    ((neutralTransform (circleUnitRotationH4 T q p hq hp) ψ).toLinearMap.comp
      ((circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j).comp
        ((neutralInverseDomainLinear (circleUnitRotationH4 T q p hq hp) ψ).comp
          (householderDomainLinear ((-I) • circleUnitRotationH4 T q p hq hp)
            (circleHouseholderAnchorH4 T)))))

theorem circle_centered_coefficient_linear_apply (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : CircleL2 T) (j : Fin 5) (f : circleH4Domain T) :
    circleCenteredCoefficientLinear T q p hq hp ψ j f =
      circleCenteredBlochCoefficient T q p hq hp ψ j f := rfl

noncomputable def circleDomainSymmetricPairing
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) (f g : circleH4Domain T) : ℂ :=
  (1/2:ℂ)*(inner ℂ (f:CircleL2 T) (A g)+inner ℂ (A f) (g:CircleL2 T))

theorem circle_domain_symmetric_add_left (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (f g u : circleH4Domain T) :
    circleDomainSymmetricPairing T A (f+g) u =
      circleDomainSymmetricPairing T A f u+circleDomainSymmetricPairing T A g u := by
  simp only [circleDomainSymmetricPairing,Submodule.coe_add,map_add,inner_add_left]
  ring

theorem circle_domain_symmetric_add_right (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (f g u : circleH4Domain T) :
    circleDomainSymmetricPairing T A u (f+g) =
      circleDomainSymmetricPairing T A u f+circleDomainSymmetricPairing T A u g := by
  simp only [circleDomainSymmetricPairing,Submodule.coe_add,map_add,inner_add_right]
  ring

theorem circle_domain_symmetric_smul_left (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (c : ℂ) (f g : circleH4Domain T) :
    circleDomainSymmetricPairing T A (c • f) g = conj c*circleDomainSymmetricPairing T A f g := by
  simp only [circleDomainSymmetricPairing,Submodule.coe_smul_of_tower,map_smul,inner_smul_left]
  ring

theorem circle_domain_symmetric_smul_right (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (c : ℂ) (f g : circleH4Domain T) :
    circleDomainSymmetricPairing T A f (c • g) = c*circleDomainSymmetricPairing T A f g := by
  simp only [circleDomainSymmetricPairing,Submodule.coe_smul_of_tower,map_smul,inner_smul_right]
  ring

theorem circle_domain_symmetric_energy (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (f : circleH4Domain T) :
    (circleDomainSymmetricPairing T A f f).re = (inner ℂ (f:CircleL2 T) (A f)).re := by
  have hrev : (inner ℂ (A f) (f:CircleL2 T)).re = (inner ℂ (f:CircleL2 T) (A f)).re := by
    rw [← inner_conj_symm]
    rfl
  simp only [circleDomainSymmetricPairing,Complex.mul_re,Complex.add_re]
  norm_num
  rw [hrev]
  ring

end Lemniscate
