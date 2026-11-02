import Lemniscate.PeriodicFiniteBlochForm
import Lemniscate.PeriodicEvenHead

/-! The exact Hermitian form decomposition used to combine the finite-head,
high-frequency and coupling estimates. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private theorem finite_householder_domain_add (e a f g : circleH4Domain T) :
    neutralHouseholderDomain e a (f+g) =
      neutralHouseholderDomain e a f+neutralHouseholderDomain e a g := by
  apply Subtype.ext
  simp only [neutral_householder_domain_coe, Submodule.coe_add, map_add]

theorem circle_finite_symmetric_add_left (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f g u : circleH4Domain T) :
    circleFiniteSymmetricCoefficient T h h₁ h₂ j (f+g) u =
      circleFiniteSymmetricCoefficient T h h₁ h₂ j f u+
        circleFiniteSymmetricCoefficient T h h₁ h₂ j g u := by
  by_cases hj : j = 0 <;>
    simp only [circleFiniteSymmetricCoefficient, hj, if_true, if_false,
      finite_householder_domain_add, Submodule.coe_add, map_add,
      inner_add_left] <;> ring

theorem circle_finite_symmetric_add_right (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (u f g : circleH4Domain T) :
    circleFiniteSymmetricCoefficient T h h₁ h₂ j u (f+g) =
      circleFiniteSymmetricCoefficient T h h₁ h₂ j u f+
        circleFiniteSymmetricCoefficient T h h₁ h₂ j u g := by
  by_cases hj : j = 0 <;>
    simp only [circleFiniteSymmetricCoefficient, hj, if_true, if_false,
      finite_householder_domain_add, Submodule.coe_add, map_add,
      inner_add_right] <;> ring

theorem circle_finite_symmetric_conj (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f g : circleH4Domain T) :
    conj (circleFiniteSymmetricCoefficient T h h₁ h₂ j f g) =
      circleFiniteSymmetricCoefficient T h h₁ h₂ j g f := by
  by_cases hj : j = 0 <;>
    simp only [circleFiniteSymmetricCoefficient, hj, if_true, if_false,
      map_mul, map_add, inner_conj_symm] <;> norm_num [map_ofNat] <;> ring

theorem circle_fixed_projection_add (f g : circleH4Domain T) :
    circleFixedProjectionH4 T (f+g) = circleFixedProjectionH4 T f+circleFixedProjectionH4 T g := by
  simp only [circleFixedProjectionH4, Submodule.coe_add, inner_add_right, add_smul]

theorem circle_finite_bloch_add_left (h h₁ h₂ : C(AddCircle T, ℂ))
    (α : ℝ) (f g u : circleH4Domain T) :
    circleFiniteBlochPairing T h h₁ h₂ α (f+g) u =
      circleFiniteBlochPairing T h h₁ h₂ α f u+circleFiniteBlochPairing T h h₁ h₂ α g u := by
  simp only [circleFiniteBlochPairing, circle_fixed_projection_add,
    add_sub_add_comm, circle_finite_symmetric_add_left,
    Submodule.coe_add, inner_add_left]
  ring

theorem circle_finite_bloch_add_right (h h₁ h₂ : C(AddCircle T, ℂ))
    (α : ℝ) (u f g : circleH4Domain T) :
    circleFiniteBlochPairing T h h₁ h₂ α u (f+g) =
      circleFiniteBlochPairing T h h₁ h₂ α u f+circleFiniteBlochPairing T h h₁ h₂ α u g := by
  simp only [circleFiniteBlochPairing, circle_fixed_projection_add,
    add_sub_add_comm, circle_finite_symmetric_add_right,
    Submodule.coe_add, inner_add_right]
  ring

theorem circle_finite_bloch_conj (h h₁ h₂ : C(AddCircle T, ℂ))
    (α : ℝ) (f g : circleH4Domain T) :
    conj (circleFiniteBlochPairing T h h₁ h₂ α f g) =
      circleFiniteBlochPairing T h h₁ h₂ α g f := by
  simp only [circleFiniteBlochPairing, map_add, map_mul, map_pow,
    Complex.conj_ofReal, inner_conj_symm, circle_finite_symmetric_conj]
  ring

theorem circle_finite_bloch_add_energy (h h₁ h₂ : C(AddCircle T, ℂ))
    (α : ℝ) (f g : circleH4Domain T) :
    (circleFiniteBlochPairing T h h₁ h₂ α (f+g) (f+g)).re =
      (circleFiniteBlochPairing T h h₁ h₂ α f f).re+
      2*(circleFiniteBlochPairing T h h₁ h₂ α f g).re+
      (circleFiniteBlochPairing T h h₁ h₂ α g g).re := by
  rw [circle_finite_bloch_add_left, circle_finite_bloch_add_right,
    circle_finite_bloch_add_right,
    ← circle_finite_bloch_conj T h h₁ h₂ α f g]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem circle_finite_bloch_head_remainder_energy (h h₁ h₂ : C(AddCircle T, ℂ))
    (α : ℝ) (f : circleH4Domain T) :
    (circleFiniteBlochPairing T h h₁ h₂ α f f).re =
      (circleFiniteBlochPairing T h h₁ h₂ α (circleEvenHeadProjection T f)
        (circleEvenHeadProjection T f)).re+
      2*(circleFiniteBlochPairing T h h₁ h₂ α (circleEvenHeadProjection T f)
        (f-circleEvenHeadProjection T f)).re+
      (circleFiniteBlochPairing T h h₁ h₂ α (f-circleEvenHeadProjection T f)
        (f-circleEvenHeadProjection T f)).re := by
  simpa only [add_sub_cancel] using circle_finite_bloch_add_energy T h h₁ h₂ α
    (circleEvenHeadProjection T f) (f-circleEvenHeadProjection T f)

end Lemniscate
