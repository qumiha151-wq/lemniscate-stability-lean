import Lemniscate.PeriodicAdjointReality

/-! Residual control of a normalized adjoint approximation. The exact vector
is supplied by the proved adjoint-kernel theorem; the trial may be any H4
vector in the even sine sector with the same normalization. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_sine_sector_sub (f g : CircleL2 T)
    (hf : InCircleEvenSineSector T f) (hg : InCircleEvenSineSector T g) :
    InCircleEvenSineSector T (f-g) := by
  constructor
  · intro n
    rw [circle_fourierCoeff_sub, circle_fourierCoeff_sub, hf.1, hg.1]
    ring
  · intro n
    rw [circle_fourierCoeff_sub, hf.2, hg.2, sub_self]

theorem circle_adjoint_residual_energy (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (ψ t : circleH4Domain T)
    (hψ : circleH4FormalAdjoint T h h₁ ψ = 0) :
    (inner ℂ ((ψ-t : circleH4Domain T) : CircleL2 T)
      (circleH4Operator T h h₁ h₂ (ψ-t))).re =
        -(inner ℂ ((ψ-t : circleH4Domain T) : CircleL2 T)
          (circleH4FormalAdjoint T h h₁ t)).re := by
  have hi : (inner ℂ ((ψ-t : circleH4Domain T) : CircleL2 T)
      (circleH4Operator T h h₁ h₂ (ψ-t))).re =
    (inner ℂ (circleH4Operator T h h₁ h₂ (ψ-t)) ((ψ-t : circleH4Domain T) : CircleL2 T)).re :=
      inner_re_symm (𝕜 := ℂ) _ _
  rw [hi, circle_h4_formal_adjoint_green T h h₁ h₂ hh hh₁ hreal h₁real h₂real,
    map_sub, hψ, zero_sub, inner_neg_right, Complex.neg_re]

theorem circle_adjoint_residual_norm_le (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (ψ t : circleH4Domain T)
    (hψ : circleH4FormalAdjoint T h h₁ ψ = 0) (gap : ℝ) (hgap : 0 < gap)
    (hd : (inner ℂ ((ψ-t : circleH4Domain T) : CircleL2 T)
      (circleH4Operator T h h₁ h₂ (ψ-t))).re ≤
        -gap*‖((ψ-t : circleH4Domain T) : CircleL2 T)‖^2) :
    ‖((ψ-t : circleH4Domain T) : CircleL2 T)‖ ≤ ‖circleH4FormalAdjoint T h h₁ t‖/gap := by
  have hb := (Complex.re_le_norm (inner ℂ ((ψ-t : circleH4Domain T) : CircleL2 T)
    (circleH4FormalAdjoint T h h₁ t))).trans
      (norm_inner_le_norm ((ψ-t : circleH4Domain T) : CircleL2 T) (circleH4FormalAdjoint T h h₁ t))
  rw [circle_adjoint_residual_energy T h h₁ h₂ hh hh₁ hreal h₁real h₂real ψ t hψ] at hd
  apply (le_div_iff₀ hgap).mpr
  by_cases hz : ‖((ψ-t : circleH4Domain T) : CircleL2 T)‖ = 0
  · rw [hz, zero_mul]
    exact norm_nonneg _
  · have hp : 0 < ‖((ψ-t : circleH4Domain T) : CircleL2 T)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_adjoint_trial_l2_error (ψ t : circleH4Domain T)
    (hψnorm : inner ℂ (ψ : CircleL2 T) (circleUnitRotation T q p) = 1)
    (htnorm : inner ℂ (t : CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hψsector : InCircleEvenSineSector T (ψ : CircleL2 T))
    (htsector : InCircleEvenSineSector T (t : CircleL2 T)) :
    ‖((ψ-t : circleH4Domain T) : CircleL2 T)‖ ≤
      ‖circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) t‖/75 := by
  have hvnorm : inner ℂ ((ψ-t : circleH4Domain T) : CircleL2 T) (circleUnitRotation T q p) = 0 := by
    change inner ℂ ((ψ : CircleL2 T)-(t : CircleL2 T)) (circleUnitRotation T q p) = 0
    rw [inner_sub_left, hψnorm, htnorm, sub_self]
  have horth : inner ℂ (circleContinuousL2 T (q*p)) ((ψ-t : circleH4Domain T) : CircleL2 T) = 0 := by
    have hv : inner ℂ (circleUnitRotation T q p) ((ψ-t : circleH4Domain T) : CircleL2 T) = 0 := by
      rw [← inner_conj_symm, hvnorm, map_zero]
    have hn : (‖circleContinuousL2 T (q*p)‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (circle_profile_rotation_ne_zero T q p hq hs hc ho))
    simp only [circleUnitRotation, inner_smul_left, map_inv₀, Complex.conj_ofReal] at hv
    exact (mul_eq_zero.mp hv).resolve_left (inv_ne_zero hn)
  have hsector : InCircleEvenSineSector T ((ψ-t : circleH4Domain T) : CircleL2 T) :=
    circle_even_sine_sector_sub T _ _ hψsector htsector
  have hd := paper_h4_operator_even_sine_sector_dissipative T q p hq hp he hqreal hpreal
    hs hc ho hr (ψ-t) hsector horth
  apply circle_adjoint_residual_norm_le T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
    _ _ _ ψ t hψzero 75 (by norm_num) hd
  · intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow, hqreal]
  · intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul, map_ofNat, hqreal, hpreal]
  · intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub, map_mul, map_one, map_ofNat, map_pow, hqreal]

end Profile
end Lemniscate
