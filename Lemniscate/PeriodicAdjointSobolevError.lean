import Lemniscate.PeriodicAdjointDerivativeBounds

/-! Residual control in the angular H4 sum norm used in the paper. The proof
uses the already proved L2 error bound, actual Gårding inequality and adjoint
equation; it does not assume a Galerkin residual certificate. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem paper_adjoint_second_norm_sq_le (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (f : circleH4Domain T) (R : ℝ) (hR : 0 ≤ R)
    (hres : ‖circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) f‖ ≤ R)
    (hmass : ‖(f : CircleL2 T)‖ ≤ R/75) :
    ‖(circleH4Jet T f).second‖^2 ≤ R^2/15 := by
  have h0real : ∀ x, conj ((q^2 : C(AddCircle T, ℂ)) x) = (q^2 : C(AddCircle T, ℂ)) x := by
    intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow, hqreal]
  have h1real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
    intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul, map_ofNat, hqreal, hpreal]
  have h2real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x) =
      (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x := by
    intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub, map_mul, map_one, map_ofNat, map_pow, hqreal]
  have hg := paper_h4_operator_garding T q p hq hp he hqreal hpreal f
  have heq : (inner ℂ (f : CircleL2 T)
      (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f)).re =
    (inner ℂ (f : CircleL2 T) (circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) f)).re := by
    calc
      _ = (inner ℂ (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f)
          (f : CircleL2 T)).re := inner_re_symm (𝕜 := ℂ) _ _
      _ = _ := congrArg Complex.re (circle_h4_formal_adjoint_green T (q^2) ((2:ℂ) • (q*p))
        (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
        (circle_profile_square_second T q p hq hp he) h0real h1real h2real f f)
  rw [heq] at hg
  have hb := Complex.re_le_norm (-inner ℂ (f : CircleL2 T)
    (circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) f))
  rw [Complex.neg_re, norm_neg] at hb
  have hi := norm_inner_le_norm (𝕜 := ℂ) (f : CircleL2 T)
    (circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) f)
  have hm := mul_le_mul hmass hres (norm_nonneg _) (by positivity : 0 ≤ R/75)
  have hm2 := pow_le_pow_left₀ (norm_nonneg _) hmass 2
  nlinarith [sq_nonneg R]

noncomputable def circleAngularH4Norm (f : circleH4Domain T) : ℝ :=
  let k := (2*Real.pi/T)⁻¹
  ‖(f : CircleL2 T)‖+k*‖(circleH4Jet T f).first‖+k^2*‖(circleH4Jet T f).second‖+
    k^3*‖(circleH4Jet T f).third‖+k^4*‖(circleH4Jet T f).fourth‖

theorem circle_angular_h4_bound_of_derivatives
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T) (R : ℝ) (hR : 0 ≤ R)
    (h0 : ‖(f : CircleL2 T)‖ ≤ R/75)
    (h1 : ‖(circleH4Jet T f).first‖ ≤ R) (h2 : ‖(circleH4Jet T f).second‖ ≤ R)
    (h3 : ‖(circleH4Jet T f).third‖ ≤ 7*R) (h4 : ‖(circleH4Jet T f).fourth‖ ≤ 38*R) :
    circleAngularH4Norm T f ≤ 177*R := by
  let k : ℝ := (2*Real.pi/T)⁻¹
  have hT : 0 < T := Fact.out
  have hfreq : 0 < 2*Real.pi/T := by positivity
  have hfreq2 : (1/2:ℝ) ≤ (2*Real.pi/T)^2 := by
    rw [hr]
    have hb : (rlo:ℝ) ≤ thetaParameter := actual_nome_theta_r_bounds.1
    norm_num [rlo] at hb
    linarith
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hk2 : k^2 ≤ 2 := by
    have heq : k^2 = 1/(2*Real.pi/T)^2 := by dsimp [k]; field_simp
    rw [heq]
    apply (div_le_iff₀ (sq_pos_of_pos hfreq)).mpr
    linarith
  have hk1 : k ≤ 3/2 := by nlinarith
  have hk3 : k^3 ≤ 3 := by
    have hm := mul_le_mul hk1 hk2 (sq_nonneg k) (by norm_num : (0:ℝ) ≤ 3/2)
    nlinarith
  have hk4 : k^4 ≤ 4 := by
    have hm := pow_le_pow_left₀ (sq_nonneg k) hk2 2
    nlinarith
  have hm1 := mul_le_mul hk1 h1 (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)
  have hm2 := mul_le_mul hk2 h2 (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  have hm3 := mul_le_mul hk3 h3 (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 3)
  have hm4 := mul_le_mul hk4 h4 (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
  change ‖(f : CircleL2 T)‖+k*‖(circleH4Jet T f).first‖+k^2*‖(circleH4Jet T f).second‖+
    k^3*‖(circleH4Jet T f).third‖+k^4*‖(circleH4Jet T f).fourth‖ ≤ _
  linarith

theorem paper_adjoint_h4_bound (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T) (R : ℝ) (hR : 0 ≤ R)
    (hres : ‖circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) f‖ ≤ R)
    (hmass : ‖(f : CircleL2 T)‖ ≤ R/75) :
    circleAngularH4Norm T f ≤ 177*R := by
  have hs := paper_adjoint_second_norm_sq_le T q p hq hp he hqreal hpreal f R hR hres hmass
  obtain ⟨h1, h2, h3, h4⟩ :=
    paper_adjoint_all_derivative_bounds T q p he hqreal hpreal f R hR hres hmass hs
  exact circle_angular_h4_bound_of_derivatives T hr f R hR hmass h1 h2 h3 h4

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
theorem paper_adjoint_trial_h4_error (ψ t : circleH4Domain T)
    (hψnorm : inner ℂ (ψ : CircleL2 T) (circleUnitRotation T q p) = 1)
    (htnorm : inner ℂ (t : CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hψsector : InCircleEvenSineSector T (ψ : CircleL2 T))
    (htsector : InCircleEvenSineSector T (t : CircleL2 T)) :
    circleAngularH4Norm T (ψ-t) ≤
      177*‖circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) t‖ := by
  have hm := paper_adjoint_trial_l2_error T q p hq hp he hqreal hpreal hs hc ho hr
    ψ t hψnorm htnorm hψzero hψsector htsector
  apply paper_adjoint_h4_bound T q p hq hp he hqreal hpreal hr (ψ-t) _ (norm_nonneg _) _ hm
  rw [map_sub, hψzero, zero_sub, norm_neg]

end Profile
end Lemniscate
