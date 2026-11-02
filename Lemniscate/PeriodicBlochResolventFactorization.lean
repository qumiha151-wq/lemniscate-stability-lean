import Lemniscate.PeriodicBlochLowerResolvent

/-! Actual factorization of lambda I-A_alpha through the established H4
principal inverse. These are identities on the full weak domain. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]
set_option maxHeartbeats 1000000

private theorem principal_h4_parameter_congr (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a = b) (f : CircleL2 T) :
    circlePrincipalResolventH4 T a ha f = circlePrincipalResolventH4 T b hb f := by
  subst b
  rfl

theorem circle_bloch_principal_first_eq (z : ℂ) (p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) :
    circleBlochPrincipalFirst T z p hp f =
      circleShiftedFirst T z (circlePrincipalResolventH4 T (p^4) (by positivity) f) := by
  have h := circle_principal_first_eq_jet T (p^2) (by nlinarith) f
  rw [principal_h4_parameter_congr T ((p^2)^2) (p^4) (by positivity) (by positivity)
    (by ring) f] at h
  change circlePrincipalFirst T (p^2) (by nlinarith) f+
    z • circlePrincipalResolvent T (p^4) (by positivity) f =
      (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).first+
        z • (circlePrincipalResolventH4 T (p^4) (by positivity) f:CircleL2 T)
  rw [h]
  rfl

theorem circle_bloch_principal_second_eq (z : ℂ) (p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) :
    circleBlochPrincipalSecond T z p hp f =
      circleShiftedSecond T z (circlePrincipalResolventH4 T (p^4) (by positivity) f) := by
  have h1 := circle_principal_first_eq_jet T (p^2) (by nlinarith) f
  have h2 := circle_principal_second_eq_jet T (p^2) (by nlinarith) f
  rw [principal_h4_parameter_congr T ((p^2)^2) (p^4) (by positivity) (by positivity)
    (by ring) f] at h1 h2
  change circlePrincipalSecond T (p^2) (by nlinarith) f+
    (2*z) • circlePrincipalFirst T (p^2) (by nlinarith) f+
    z^2 • circlePrincipalResolvent T (p^4) (by positivity) f =
      (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).second+
        (2*z) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).first+
        z^2 • (circlePrincipalResolventH4 T (p^4) (by positivity) f:CircleL2 T)
  rw [h1,h2]
  rfl

theorem circle_bloch_principal_correction_eq (z : ℂ) (p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) :
    circleBlochPrincipalCorrection T z p hp f =
      (-4:ℂ) • circleShiftedFourth T z (circlePrincipalResolventH4 T (p^4) (by positivity) f)-
        (-4:ℂ) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).fourth := by
  have h1 := circle_principal_first_eq_jet T (p^2) (by nlinarith) f
  have h2 := circle_principal_second_eq_jet T (p^2) (by nlinarith) f
  rw [principal_h4_parameter_congr T ((p^2)^2) (p^4) (by positivity) (by positivity)
    (by ring) f] at h1 h2
  simp only [circleBlochPrincipalCorrection,add_apply,smul_apply,h1,h2,circle_principal_third_eq_jet]
  change _ = (-4:ℂ) •
    ((circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).fourth+
      (4*z) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).third+
      (6*z^2) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).second+
      (4*z^3) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).first+
      z^4 • (circlePrincipalResolventH4 T (p^4) (by positivity) f:CircleL2 T))-
    (-4:ℂ) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).fourth
  change (-16*z) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).third+
      (-24*z^2) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).second+
      (-16*z^3) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).first+
      (-4*z^4) • (circlePrincipalResolventH4 T (p^4) (by positivity) f:CircleL2 T) = _
  module

noncomputable def circleBlochComplexShift (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) (w : ℂ) :
    circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  w • (circleH4Domain T).subtype-circleBlochOperator T h h₁ h₂ α

theorem circle_bloch_operator_principal (h h₁ h₂ : C(AddCircle T, ℂ))
    (α p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) :
    circleBlochOperator T h h₁ h₂ α (circlePrincipalResolventH4 T (p^4) (by positivity) f) =
      (-4:ℂ) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).fourth+
        circleBlochLowerResolvent T h h₁ h₂ α p hp f := by
  have hcoe : (circlePrincipalResolventH4 T (p^4) (by positivity) f:CircleL2 T) =
      circlePrincipalResolvent T (p^4) (by positivity) f := rfl
  simp only [circleBlochOperator,circleBlochLowerResolvent,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,LinearMap.comp_apply,Submodule.subtype_apply,
    add_apply,sub_apply,smul_apply,
    ContinuousLinearMap.comp_apply,circle_bloch_principal_first_eq,circle_bloch_principal_second_eq,
    circle_bloch_principal_correction_eq,hcoe]
  module

theorem circle_bloch_shift_principal (h h₁ h₂ : C(AddCircle T, ℂ))
    (α p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) :
    circleBlochComplexShift T h h₁ h₂ α (p^4:ℝ)
      (circlePrincipalResolventH4 T (p^4) (by positivity) f) =
      f-circleBlochLowerResolvent T h h₁ h₂ α p hp f := by
  have hi := circle_principal_resolvent_right_inverse T (p^4) (by positivity) f
  change ((p^4:ℝ):ℂ) • (circlePrincipalResolventH4 T (p^4) (by positivity) f:CircleL2 T)+
    (4:ℂ) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).fourth = f at hi
  change ((p^4:ℝ):ℂ) • (circlePrincipalResolventH4 T (p^4) (by positivity) f:CircleL2 T)-
    circleBlochOperator T h h₁ h₂ α (circlePrincipalResolventH4 T (p^4) (by positivity) f) = _
  rw [circle_bloch_operator_principal T h h₁ h₂ α p hp f]
  calc
    _ = (((p^4:ℝ):ℂ) • (circlePrincipalResolventH4 T (p^4) (by positivity) f:CircleL2 T)+
      (4:ℂ) • (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).fourth)-
        circleBlochLowerResolvent T h h₁ h₂ α p hp f := by module
    _ = _ := by rw [hi]

theorem circle_bloch_shift_factorization (h h₁ h₂ : C(AddCircle T, ℂ))
    (α p : ℝ) (hp : 1 ≤ p) (u : circleH4Domain T) :
    circleBlochComplexShift T h h₁ h₂ α (p^4:ℝ) u =
      (1-circleBlochLowerResolvent T h h₁ h₂ α p hp) (circlePrincipalShift T (p^4) u) := by
  have h := circle_bloch_shift_principal T h h₁ h₂ α p hp (circlePrincipalShift T (p^4) u)
  rw [circle_principal_resolvent_h4_left_inverse] at h
  simpa only [sub_apply,one_apply_eq_self] using h

end Lemniscate
