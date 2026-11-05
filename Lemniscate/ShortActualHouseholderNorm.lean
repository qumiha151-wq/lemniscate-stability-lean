import Lemniscate.ShortHouseholderWeightedBounds
import Lemniscate.ShortFiniteHouseholderData
import Lemniscate.ShortAdjointRotationError

/-! The actual and seven-mode Householder maps satisfy the same weighted
bounds.  The finite rational margins absorb the proved full Fourier tail. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

private theorem inverse_weight_perturbation (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n)
    (e e₇ a : circleH4Domain T) :
    ‖shortInverseWeightFourier T w hw ((e+a : circleH4Domain T) : CircleL2 T)‖ ≤
      ‖((e-e₇ : circleH4Domain T) : CircleL2 T)‖ +
        ‖shortInverseWeightFourier T w hw ((e₇+a : circleH4Domain T) : CircleL2 T)‖ := by
  let D := shortInverseWeightFourierCLM T w hw
  have hD (f : CircleL2 T) : ‖D f‖ ≤ ‖f‖ := by
    have h := D.le_opNorm f
    have hn : ‖D‖ ≤ 1 := short_inverse_fourier_clm_norm_le T w hw
    exact h.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg f))
  have he : ((e+a : circleH4Domain T) : CircleL2 T) =
      ((e-e₇ : circleH4Domain T) : CircleL2 T) +
        ((e₇+a : circleH4Domain T) : CircleL2 T) := by
    simp only [Submodule.coe_add,Submodule.coe_sub]
    abel
  change ‖D ((e+a : circleH4Domain T) : CircleL2 T)‖ ≤ _
  rw [he,map_add]
  exact (norm_add_le _ _).trans (add_le_add (hD _) le_rfl)

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

/-- Both actual maps have the same explicit weighted operator bounds;
the denominators have a common positive lower bound. -/
theorem short_actual_householder_operator_bounds :
    let e := circleShortRotationVector T q p hq hp
    let e₇ := circleShortRotationApproximation T
    let a := circleHouseholderAnchorH4 T
    (19/10:ℝ) ≤ (1+inner ℂ (e : CircleL2 T) (a : CircleL2 T)).re ∧
    (19/10:ℝ) ≤ (1+inner ℂ (e₇ : CircleL2 T) (a : CircleL2 T)).re ∧
    ∀ f : circleH4Domain T,
      shortVNorm T (neutralHouseholderDomain e a f) ≤ (3/2:ℝ)*shortVNorm T f ∧
      shortH1Norm T (neutralHouseholderDomain e a f) ≤ (6/5:ℝ)*shortH1Norm T f ∧
      shortVNorm T (neutralHouseholderDomain e₇ a f) ≤ (3/2:ℝ)*shortVNorm T f ∧
      shortH1Norm T (neutralHouseholderDomain e₇ a f) ≤ (6/5:ℝ)*shortH1Norm T f := by
  let e := circleShortRotationVector T q p hq hp
  let e₇ := circleShortRotationApproximation T
  let a := circleHouseholderAnchorH4 T
  have herr := short_actual_rotation_approximation_error T q p hq hp he hqreal hpreal hs hc ho hr
  change ‖((e-e₇ : circleH4Domain T) : CircleL2 T)‖ < (1/160000:ℝ)/250 ∧
    shortH1Norm T (e-e₇) < (1/160000:ℝ)/16 ∧
      shortVNorm T (e-e₇) < (1/160000:ℝ) at herr
  obtain ⟨d₇, hd₇, hden₇, hV₇, hDV₇, hH₇, hDH₇⟩ := short_finite_householder_data T
  change 1+inner ℂ (e₇ : CircleL2 T) (a : CircleL2 T) = (d₇ : ℂ) at hden₇
  obtain ⟨c,hc0,hca,hce⟩ := circle_unit_rotation_phase_anchor T q p hq hs hc ho
  let d := 1+c
  have hpa : inner ℂ (a : CircleL2 T) (e : CircleL2 T) = (c : ℂ) := hca
  have hpe : inner ℂ (e : CircleL2 T) (a : CircleL2 T) = (c : ℂ) := hce
  have hden : 1+inner ℂ (e : CircleL2 T) (a : CircleL2 T) = (d : ℂ) := by
    rw [hpe]
    simp only [d,Complex.ofReal_add,Complex.ofReal_one]
  have ha : inner ℂ (a : CircleL2 T) (a : CircleL2 T) = 1 := circle_householder_anchor_unit T
  have han : ‖(a : CircleL2 T)‖ = 1 := by
    have hn : ‖(a : CircleL2 T)‖^2 = 1 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ),ha]
      rfl
    nlinarith only [hn,norm_nonneg (a : CircleL2 T)]
  have hpair : ((d-d₇ : ℝ) : ℂ) =
      inner ℂ (((e-e₇ : circleH4Domain T) : CircleL2 T)) (a : CircleL2 T) := by
    simp only [Submodule.coe_sub,inner_sub_left,Complex.ofReal_sub]
    linear_combination -hden+hden₇
  have hdd : |d-d₇| ≤ ‖((e-e₇ : circleH4Domain T) : CircleL2 T)‖ := by
    calc
      _ = ‖((d-d₇ : ℝ) : ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs]
      _ = _ := congrArg norm hpair
      _ ≤ ‖((e-e₇ : circleH4Domain T) : CircleL2 T)‖*‖(a : CircleL2 T)‖ :=
        norm_inner_le_norm _ _
      _ = _ := by rw [han,mul_one]
  have hd : (99/50:ℝ) ≤ d := by
    have hdiff := neg_abs_le (d-d₇)
    nlinarith only [hd₇,hdd,herr.1,hdiff]
  have hunit : inner ℂ (e : CircleL2 T) (e : CircleL2 T) = 1 := by
    apply inner_self_eq_one_of_norm_eq_one
    have hn : ‖circleUnitRotation T q p‖ = 1 := by
      simpa only [norm_neg] using
        short_positive_rotation_norm T q p hq hp he hqreal hpreal hs hc ho hr
    change ‖(-I) • circleUnitRotation T q p‖ = 1
    simp only [norm_smul,norm_neg,Complex.norm_I,one_mul,hn]
  have hunit₇ : inner ℂ (e₇ : CircleL2 T) (e₇ : CircleL2 T) = 1 :=
    inner_self_eq_one_of_norm_eq_one (short_actual_finite_vector_bounds T).1
  have hsym : inner ℂ (a : CircleL2 T) (e : CircleL2 T) =
      inner ℂ (e : CircleL2 T) (a : CircleL2 T) := hpa.trans hpe.symm
  have hsym₇ : inner ℂ (a : CircleL2 T) (e₇ : CircleL2 T) =
      inner ℂ (e₇ : CircleL2 T) (a : CircleL2 T) := (short_finite_householder_symmetries T).1
  have hu : e+a = (e-e₇)+(e₇+a) := by abel
  have hV : shortVNorm T (e+a) ≤ 17/2 := by
    have h := short_v_norm_add_le T (e-e₇) (e₇+a)
    rw [← hu] at h
    linarith only [h,herr.2.2,hV₇]
  have hH : shortH1Norm T (e+a) ≤ 9/2 := by
    have h := short_h1_norm_add_le T (e-e₇) (e₇+a)
    rw [← hu] at h
    linarith only [h,herr.2.1,hH₇]
  have hDV : ‖shortInverseWeightFourier T Lemniscate.shortVWeight short_v_weight_one_le
      ((e+a : circleH4Domain T) : CircleL2 T)‖ ≤ 1/2 := by
    have h := inverse_weight_perturbation T Lemniscate.shortVWeight short_v_weight_one_le e e₇ a
    linarith only [h,herr.1,hDV₇]
  have hDH : ‖shortInverseWeightFourier T Lemniscate.shortH1Weight short_h1_weight_one_le
      ((e+a : circleH4Domain T) : CircleL2 T)‖ ≤ 89/100 := by
    have h := inverse_weight_perturbation T Lemniscate.shortH1Weight short_h1_weight_one_le e e₇ a
    linarith only [h,herr.1,hDH₇]
  have htrue := short_weighted_householder_operator_bounds T e a hunit ha hsym d hd hden hV hDV hH hDH
  have hfinite := short_weighted_householder_operator_bounds T e₇ a hunit₇ ha hsym₇ d₇
    (by linarith only [hd₇]) hden₇
    (by linarith only [hV₇]) (by linarith only [hDV₇])
    (by linarith only [hH₇]) (by linarith only [hDH₇])
  refine ⟨?_,?_,fun f => ⟨(htrue f).1,(htrue f).2,(hfinite f).1,(hfinite f).2⟩⟩
  · rw [hden,Complex.ofReal_re]
    linarith only [hd]
  · rw [hden₇,Complex.ofReal_re]
    linarith only [hd₇]

end Profile
end Lemniscate
