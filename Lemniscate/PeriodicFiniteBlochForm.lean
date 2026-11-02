import Lemniscate.PeriodicFiniteHighEnergy
import Lemniscate.PeriodicBlochHighFrequency
import Lemniscate.PeriodicBlochParity

/-! The finite approximation of the polynomial after cancellation of the
neutral factors. Its high-frequency part is the actual Bloch energy. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFixedProjectionH4 (f : circleH4Domain T) : circleH4Domain T :=
  inner ℂ (circleHouseholderAnchor T) (f : CircleL2 T) • circleHouseholderAnchorH4 T

/-- The constant coefficient is the pullback of the symmetric part of A0.
Only positive-degree coefficients use the approximate neutral transform. -/
noncomputable def circleFiniteSymmetricCoefficient (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f g : circleH4Domain T) : ℂ :=
  if j = 0 then
    let Uf := neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f
    let Ug := neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) g
    (1/2:ℂ)*(inner ℂ (Uf : CircleL2 T) (circleBlochCoefficient T h h₁ h₂ 0 Ug)+
      inner ℂ (circleBlochCoefficient T h h₁ h₂ 0 Uf) (Ug : CircleL2 T))
  else (1/2:ℂ)*(inner ℂ (f : CircleL2 T)
      (circleFiniteTransformedOperator T (circleBlochCoefficient T h h₁ h₂ j) g)+
    inner ℂ (circleFiniteTransformedOperator T (circleBlochCoefficient T h h₁ h₂ j) f)
      (g : CircleL2 T))

noncomputable def circleFiniteBlochPairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (α : ℝ) (f g : circleH4Domain T) : ℂ :=
  let H := circleFiniteSymmetricCoefficient T h h₁ h₂
  let f₀ := circleFixedProjectionH4 T f
  let g₀ := circleFixedProjectionH4 T g
  let f₁ := f-f₀
  let g₁ := g-g₀
  let c : ℂ := ((-4*(2*Real.pi/T)^4:ℝ):ℂ)
  H 2 f₀ g₀+c*(α:ℂ)^2*inner ℂ (f₀ : CircleL2 T) (g₀ : CircleL2 T)+
    (H 1 f₀ g₁+H 1 f₁ g₀)+
    (α:ℂ)*(H 2 f₀ g₁+H 2 f₁ g₀)+
    (α:ℂ)^2*(H 3 f₀ g₁+H 3 f₁ g₀)+
    H 0 f₁ g₁+(α:ℂ)*H 1 f₁ g₁+(α:ℂ)^2*H 2 f₁ g₁+
    (α:ℂ)^3*H 3 f₁ g₁+c*(α:ℂ)^4*inner ℂ (f₁ : CircleL2 T) (g₁ : CircleL2 T)

theorem circle_finite_zero_coefficient (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (f g : circleH4Domain T) :
    circleFiniteSymmetricCoefficient T h h₁ h₂ 0 f g =
      inner ℂ (neutralHouseholderDomain (circleFiniteRotationPhase T)
        (circleHouseholderAnchorH4 T) f : CircleL2 T)
        (circleH4SymmetricOperator T h h₁ h₂
          (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) g)) := by
  let Uf := neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f
  let Ug := neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) g
  change (1/2:ℂ)*(inner ℂ (Uf : CircleL2 T) (circleH4Operator T h h₁ h₂ Ug)+
    inner ℂ (circleH4Operator T h h₁ h₂ Uf) (Ug : CircleL2 T)) =
      inner ℂ (Uf : CircleL2 T) (circleH4SymmetricOperator T h h₁ h₂ Ug)
  rw [circle_h4_formal_adjoint_green T h h₁ h₂ hh hh₁ hreal h₁real h₂real Uf Ug,
    circle_h4_formal_adjoint_split T h h₁ h₂ Ug, circle_h4_operator_apply]
  unfold circleLinearL2Expression
  rw [← circle_h4_symmetric_operator_apply T h h₁ h₂ Ug]
  simp only [inner_add_right, inner_sub_right]
  ring

private theorem finite_symmetric_zero_left (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f : circleH4Domain T) :
    circleFiniteSymmetricCoefficient T h h₁ h₂ j 0 f = 0 := by
  simp [circleFiniteSymmetricCoefficient, neutralHouseholderDomain]

private theorem finite_symmetric_zero_right (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f : circleH4Domain T) :
    circleFiniteSymmetricCoefficient T h h₁ h₂ j f 0 = 0 := by
  simp [circleFiniteSymmetricCoefficient, neutralHouseholderDomain]

theorem circle_finite_bloch_high_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (α : ℝ) (f : circleH4Domain T)
    (hf : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (f : CircleL2 T) n = 0) :
    (circleFiniteBlochPairing T h h₁ h₂ α f f).re =
      (inner ℂ (f : CircleL2 T) (circleBlochOperator T h h₁ h₂ α f)).re := by
  have hP : circleFixedProjectionH4 T f = 0 := by
    rw [circleFixedProjectionH4, circle_householder_anchor_pairing,
      hf 2 (by norm_num), hf (-2) (by norm_num)]
    simp
  have hdiag (j : Fin 5) :
      (circleFiniteSymmetricCoefficient T h h₁ h₂ j f f).re =
        (inner ℂ (f : CircleL2 T) (circleBlochCoefficient T h h₁ h₂ j f)).re := by
    have hs (x y : CircleL2 T) :
        ((1/2:ℂ)*(inner ℂ x y+inner ℂ y x)).re = (inner ℂ x y).re := by
      have hr : (inner ℂ y x).re = (inner ℂ x y).re := by
        rw [← inner_conj_symm]
        rfl
      simp only [Complex.mul_re, Complex.add_re]
      norm_num
      rw [hr]
      ring
    by_cases hj : j = 0
    · subst j
      rcases circle_finite_high_pairings T f hf with ⟨he, _, ha⟩
      have hU : neutralHouseholderDomain (circleFiniteRotationPhase T)
          (circleHouseholderAnchorH4 T) f = f := by
        simp only [neutralHouseholderDomain, circle_householder_anchor_h4_coe,
          inner_add_left, he, ha, add_zero, mul_zero, zero_smul, sub_zero]
      simp only [circleFiniteSymmetricCoefficient, if_pos rfl, hU]
      exact hs _ _
    · simp only [circleFiniteSymmetricCoefficient, if_neg hj]
      rw [hs, circle_finite_transform_high_energy T _ f hf]
  have hexp := congrArg (fun v : CircleL2 T => (inner ℂ (f : CircleL2 T) v).re)
    (circle_bloch_polynomial T h h₁ h₂ α f)
  rw [circle_bloch_top_coefficient T h h₁ h₂ ((2*Real.pi/T)^2) rfl] at hexp
  simp only [circleFiniteBlochPairing, hP, sub_zero,
    finite_symmetric_zero_left, finite_symmetric_zero_right,
    Submodule.coe_zero, inner_zero_left, inner_zero_right, mul_zero, zero_add, add_zero,
    inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
    ← Complex.ofReal_pow, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hdiag] at hexp ⊢
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, norm_zero, zero_mul, mul_zero, sub_zero, add_zero] at hexp ⊢
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add] at hexp ⊢
  nlinarith only [hexp]

theorem paper_finite_bloch_high_energy (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hr : (7/10:ℝ) ≤ (2*Real.pi/T)^2) (α : ℝ) (hα : |α| ≤ 1/2)
    (f : circleH4Domain T)
    (hf : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (f : CircleL2 T) n = 0) :
    (circleFiniteBlochPairing T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f f).re ≤
      -(1/2:ℝ)*(∑' n : ℤ, (n:ℝ)^4*‖fourierCoeff (f : CircleL2 T) n‖^2) := by
  rw [circle_finite_bloch_high_pairing T _ _ _ α f hf]
  exact paper_bloch_high_frequency_energy T q p hq hp he hqreal hpreal hr α hα f hf

end Lemniscate
