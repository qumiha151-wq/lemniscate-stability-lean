import Lemniscate.PeriodicThirdResolvent
import Lemniscate.PeriodicBlochPolynomial
import Lemniscate.PeriodicResolventPerturbation

/-! The Bloch lower-order part composed with the existing principal
resolvent at p^4. A common coarse bound is enough for the Neumann argument. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleBlochPrincipalFirst (z : ℂ) (p : ℝ) (hp : 1 ≤ p) :
    CircleL2 T →L[ℂ] CircleL2 T :=
  circlePrincipalFirst T (p^2) (by nlinarith) +
    z • circlePrincipalResolvent T (p^4) (by positivity)

noncomputable def circleBlochPrincipalSecond (z : ℂ) (p : ℝ) (hp : 1 ≤ p) :
    CircleL2 T →L[ℂ] CircleL2 T :=
  circlePrincipalSecond T (p^2) (by nlinarith) +
    (2*z) • circlePrincipalFirst T (p^2) (by nlinarith) +
    z^2 • circlePrincipalResolvent T (p^4) (by positivity)

noncomputable def circleBlochPrincipalCorrection (z : ℂ) (p : ℝ) (hp : 1 ≤ p) :
    CircleL2 T →L[ℂ] CircleL2 T :=
  (-16*z) • circlePrincipalThird T p (by linarith) +
    (-24*z^2) • circlePrincipalSecond T (p^2) (by nlinarith) +
    (-16*z^3) • circlePrincipalFirst T (p^2) (by nlinarith) +
    (-4*z^4) • circlePrincipalResolvent T (p^4) (by positivity)

noncomputable def circleBlochLowerResolvent (h h₁ h₂ : C(AddCircle T, ℂ))
    (α p : ℝ) (hp : 1 ≤ p) : CircleL2 T →L[ℂ] CircleL2 T :=
  let z := (α:ℂ)*circleFrequencyFactor T 1
  circleBlochPrincipalCorrection T z p hp -
    (45:ℂ) • (circleMultiplyL2 T h).comp (circleBlochPrincipalSecond T z p hp) -
    (75/2:ℂ) • (circleMultiplyL2 T h₁).comp (circleBlochPrincipalFirst T z p hp) -
    (42:ℂ) • circlePrincipalResolvent T (p^4) (by positivity) +
    (15/2:ℂ) • (circleMultiplyL2 T h₂).comp (circlePrincipalResolvent T (p^4) (by positivity))

private theorem low_resolvent_norms (p : ℝ) (hp : 1 ≤ p) :
    ‖circlePrincipalResolvent T (p^4) (by positivity)‖ ≤ 2/p ∧
    ‖circlePrincipalFirst T (p^2) (by nlinarith)‖ ≤ 2/p ∧
    ‖circlePrincipalSecond T (p^2) (by nlinarith)‖ ≤ 2/p ∧
    ‖circlePrincipalThird T p (by linarith)‖ ≤ 2/p := by
  have hp0 : 0 < p := by linarith
  have hp2 : p ≤ p^2 := by nlinarith
  have hp4 : p ≤ p^4 := by nlinarith only [hp2,pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hp 4]
  refine ⟨?_,?_,?_,circle_principal_third_norm_le T p hp0⟩
  · apply (circle_principal_resolvent_norm_le T (p^4) (by positivity)).trans
    rw [← one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < p^4) hp0).mpr
    nlinarith only [hp4,pow_nonneg hp0.le 4]
  · apply (circle_principal_first_norm_le T (p^2) (by nlinarith)).trans
    apply (div_le_div_iff₀ (by positivity : 0 < 4*p^2) hp0).mpr
    nlinarith only [hp2,hp0]
  · apply (circle_principal_second_norm_le T (p^2) (by nlinarith)).trans
    apply (div_le_div_iff₀ (by positivity : 0 < 4*p^2) hp0).mpr
    nlinarith only [hp2,hp0]

set_option maxHeartbeats 1000000 in
theorem circle_bloch_principal_lower_bounds (z : ℂ) (hz : ‖z‖ ≤ 1) (p : ℝ) (hp : 1 ≤ p) :
    ‖circleBlochPrincipalFirst T z p hp‖ ≤ 4/p ∧
    ‖circleBlochPrincipalSecond T z p hp‖ ≤ 8/p ∧
    ‖circleBlochPrincipalCorrection T z p hp‖ ≤ 120/p := by
  rcases low_resolvent_norms T p hp with ⟨h0,h1,h2,h3⟩
  have hq : 0 ≤ 2/p := by positivity
  have hscale (k : ℕ) (R : CircleL2 T →L[ℂ] CircleL2 T) (hR : ‖R‖ ≤ 2/p) :
      ‖z^k • R‖ ≤ 2/p := by
    rw [norm_smul,norm_pow]
    have hk : ‖z‖^k ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg z) hz k
    simpa only [one_mul] using mul_le_mul hk hR (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have s0 := hscale 4 _ h0
  have s1 := hscale 3 _ h1
  have s2 := hscale 2 _ h2
  have s3 := hscale 1 _ h3
  refine ⟨?_,?_,?_⟩
  · have h := norm_add_le (circlePrincipalFirst T (p^2) (by nlinarith))
      (z • circlePrincipalResolvent T (p^4) (by positivity))
    have hs := hscale 1 _ h0
    simp only [pow_one] at hs
    change ‖circlePrincipalFirst T (p^2) (by nlinarith)+z • circlePrincipalResolvent T (p^4) (by positivity)‖ ≤ _
    simp only [div_eq_mul_inv] at h1 hs ⊢
    nlinarith only [h,h1,hs]
  · have hs1 := hscale 1 _ h1
    simp only [pow_one] at hs1
    have h : ‖circlePrincipalSecond T (p^2) (by nlinarith)+(2*z) • circlePrincipalFirst T (p^2) (by nlinarith)+
        z^2 • circlePrincipalResolvent T (p^4) (by positivity)‖ ≤
      ‖circlePrincipalSecond T (p^2) (by nlinarith)‖+‖(2*z) • circlePrincipalFirst T (p^2) (by nlinarith)‖+
        ‖z^2 • circlePrincipalResolvent T (p^4) (by positivity)‖ := norm_add₃_le
    have hs : ‖(2*z) • circlePrincipalFirst T (p^2) (by nlinarith)‖ ≤ 4/p := by
      rw [mul_smul,norm_smul]
      norm_num only [Complex.norm_ofNat]
      simp only [div_eq_mul_inv] at hs1 ⊢
      nlinarith only [hs1]
    change ‖circlePrincipalSecond T (p^2) (by nlinarith)+(2*z) • circlePrincipalFirst T (p^2) (by nlinarith)+
      z^2 • circlePrincipalResolvent T (p^4) (by positivity)‖ ≤ _
    have hs0 := hscale 2 _ h0
    simp only [div_eq_mul_inv] at h2 hs hs0 ⊢
    nlinarith only [h,h2,hs,hs0]
  · have h : ‖(-16*z) • circlePrincipalThird T p (by linarith)+
        (-24*z^2) • circlePrincipalSecond T (p^2) (by nlinarith)+
        (-16*z^3) • circlePrincipalFirst T (p^2) (by nlinarith)+
        (-4*z^4) • circlePrincipalResolvent T (p^4) (by positivity)‖ ≤
      ‖(-16*z) • circlePrincipalThird T p (by linarith)‖+
        ‖(-24*z^2) • circlePrincipalSecond T (p^2) (by nlinarith)‖+
        ‖(-16*z^3) • circlePrincipalFirst T (p^2) (by nlinarith)‖+
        ‖(-4*z^4) • circlePrincipalResolvent T (p^4) (by positivity)‖ := norm_add₄_le
    simp only [mul_smul,norm_smul] at h s0 s1 s2 s3
    norm_num only [norm_neg,Complex.norm_ofNat] at h
    simp only [pow_one] at s3
    change ‖(-16*z) • circlePrincipalThird T p (by linarith)+
      (-24*z^2) • circlePrincipalSecond T (p^2) (by nlinarith)+
      (-16*z^3) • circlePrincipalFirst T (p^2) (by nlinarith)+
      (-4*z^4) • circlePrincipalResolvent T (p^4) (by positivity)‖ ≤ _
    simp only [mul_smul]
    simp only [div_eq_mul_inv] at s0 s1 s2 s3 ⊢
    nlinarith only [h,s0,s1,s2,s3]

set_option maxHeartbeats 1000000 in
theorem circle_bloch_lower_resolvent_norm_le (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : ‖h‖ ≤ 1) (hh₁ : ‖h₁‖ ≤ 2) (hh₂ : ‖h₂‖ ≤ 4)
    (α p : ℝ) (hp : 1 ≤ p) (hz : ‖(α:ℂ)*circleFrequencyFactor T 1‖ ≤ 1) :
    ‖circleBlochLowerResolvent T h h₁ h₂ α p hp‖ ≤ 1000/p := by
  let z := (α:ℂ)*circleFrequencyFactor T 1
  rcases circle_bloch_principal_lower_bounds T z hz p hp with ⟨h1,h2,h4⟩
  have h0 := (low_resolvent_norms T p hp).1
  have m1 := (circle_multiply_comp_norm_le T h₁ _ _ h1).trans
    (mul_le_mul_of_nonneg_right hh₁ (by positivity : 0 ≤ 4/p))
  have m2 := (circle_multiply_comp_norm_le T h _ _ h2).trans
    (mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 8/p))
  have m0 := (circle_multiply_comp_norm_le T h₂ _ _ h0).trans
    (mul_le_mul_of_nonneg_right hh₂ (by positivity : 0 ≤ 2/p))
  let A := circleBlochPrincipalCorrection T z p hp
  let B := (45:ℂ) • (circleMultiplyL2 T h).comp (circleBlochPrincipalSecond T z p hp)
  let C := (75/2:ℂ) • (circleMultiplyL2 T h₁).comp (circleBlochPrincipalFirst T z p hp)
  let D := (42:ℂ) • circlePrincipalResolvent T (p^4) (by positivity)
  let E := (15/2:ℂ) • (circleMultiplyL2 T h₂).comp (circlePrincipalResolvent T (p^4) (by positivity))
  have t1 := norm_sub_le A B
  have t2 := norm_sub_le (A-B) C
  have t3 := norm_sub_le (A-B-C) D
  have t4 := norm_add_le (A-B-C-D) E
  have nB : ‖B‖ ≤ 360/p := by
    dsimp only [B]; rw [norm_smul]; norm_num only [Complex.norm_ofNat]
    simp only [div_eq_mul_inv] at m2 ⊢
    nlinarith only [m2]
  have nC : ‖C‖ ≤ 300/p := by
    dsimp only [C]; rw [norm_smul]; norm_num
    simp only [div_eq_mul_inv] at m1 ⊢
    nlinarith only [m1]
  have nD : ‖D‖ ≤ 84/p := by
    dsimp only [D]; rw [norm_smul]; norm_num only [Complex.norm_ofNat]
    simp only [div_eq_mul_inv] at h0 ⊢
    nlinarith only [h0]
  have nE : ‖E‖ ≤ 60/p := by
    dsimp only [E]; rw [norm_smul]; norm_num
    simp only [div_eq_mul_inv] at m0 ⊢
    nlinarith only [m0]
  change ‖A-B-C-D+E‖ ≤ _
  change ‖A‖ ≤ 120/p at h4
  simp only [div_eq_mul_inv] at h4 nB nC nD nE ⊢
  nlinarith only [t1,t2,t3,t4,h4,nB,nC,nD,nE,show 0 ≤ p⁻¹ by positivity]

end Lemniscate
