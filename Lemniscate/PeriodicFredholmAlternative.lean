import Lemniscate.PeriodicComplexShift
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-! The Fredholm alternative for the actual H4-domain differential operator.
The resolvent set means existence of a bounded L2 inverse with range in H4
and both inverse identities. No boundedness of the differential operator on
L2 is assumed. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

def CircleInverseIdentities (h h₁ h₂ : C(AddCircle T, ℂ))
    (z : ℂ) (R : CircleL2 T →L[ℂ] CircleL2 T) : Prop :=
  (∀ f : CircleL2 T, ∃ u : circleH4Domain T,
    (u : CircleL2 T) = R f ∧ circleComplexShift T h h₁ h₂ z u = f) ∧
  (∀ u : circleH4Domain T, R (circleComplexShift T h h₁ h₂ z u) = (u : CircleL2 T))

def circleResolventSet (h h₁ h₂ : C(AddCircle T, ℂ)) : Set ℂ :=
  {z | ∃ R : CircleL2 T →L[ℂ] CircleL2 T, CircleInverseIdentities T h h₁ h₂ z R}

def circleSpectrum (h h₁ h₂ : C(AddCircle T, ℂ)) : Set ℂ :=
  (circleResolventSet T h h₁ h₂)ᶜ

theorem circle_complex_inverse_of_unit (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1)
    (z : ℂ) (U : (CircleL2 T →L[ℂ] CircleL2 T)ˣ)
    (hU : (U : CircleL2 T →L[ℂ] CircleL2 T) =
      1-circleResolventFeedback T h h₁ h₂ p hp hK z) :
    ∃ R : CircleL2 T →L[ℂ] CircleL2 T,
      IsCompactOperator R ∧ CircleInverseIdentities T h h₁ h₂ z R := by
  let Q : CircleL2 T →L[ℂ] CircleL2 T := ↑U⁻¹
  have hright (f : CircleL2 T) :
      (U : CircleL2 T →L[ℂ] CircleL2 T) (Q f) = f := by
    simpa only [mul_apply_eq_comp, one_apply_eq_self, Q] using
      congrArg (fun L : CircleL2 T →L[ℂ] CircleL2 T => L f) (Units.mul_inv U)
  have hleft (f : CircleL2 T) :
      Q ((U : CircleL2 T →L[ℂ] CircleL2 T) f) = f := by
    simpa only [mul_apply_eq_comp, one_apply_eq_self, Q] using
      congrArg (fun L : CircleL2 T →L[ℂ] CircleL2 T => L f) (Units.inv_mul U)
  refine ⟨(circleFullResolvent T h h₁ h₂ p hp hK).comp Q, ?_, ?_⟩
  · change IsCompactOperator
      ((circleFullResolvent T h h₁ h₂ p hp hK : CircleL2 T → CircleL2 T) ∘ Q)
    exact IsCompactOperator.comp_clm
      (f := (circleFullResolvent T h h₁ h₂ p hp hK : CircleL2 T → CircleL2 T))
      (circle_full_resolvent_compact T h h₁ h₂ p hp hK) Q
  · constructor
    · intro f
      refine ⟨circleFullResolventH4 T h h₁ h₂ p hp hK (Q f), rfl, ?_⟩
      rw [circle_complex_shift_resolvent, ← hU]
      exact hright f
    · intro u
      simp only [ContinuousLinearMap.comp_apply]
      rw [circle_complex_shift_factorization T h h₁ h₂ p hp hK z u, ← hU,
        hleft, circle_full_resolvent_left_inverse]

theorem circle_complex_shift_alternative (h h₁ h₂ : C(AddCircle T, ℂ)) (z : ℂ) :
    (∃ u : circleH4Domain T, (u : CircleL2 T) ≠ 0 ∧ circleComplexShift T h h₁ h₂ z u = 0) ∨
    (∃ R : CircleL2 T →L[ℂ] CircleL2 T,
      IsCompactOperator R ∧ CircleInverseIdentities T h h₁ h₂ z R) := by
  let p := circleResolventScale T h h₁ h₂
  have hp : 1 ≤ p := circle_resolvent_scale_ge_one T h h₁ h₂
  have hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1 :=
    circle_lower_resolvent_norm_lt_one T h h₁ h₂
  let F := circleResolventFeedback T h h₁ h₂ p hp hK z
  have hF : IsCompactOperator F := circle_resolvent_feedback_compact T h h₁ h₂ p hp hK z
  rcases hF.hasEigenvalue_or_mem_resolventSet (by norm_num : (1:ℂ) ≠ 0) with he | hr
  · left
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hvne : v ≠ 0 := hv.2
    have hfv : F v = v := by
      have heq := hv.apply_eq_smul
      change F v = (1:ℂ) • v at heq
      simpa only [one_smul] using heq
    refine ⟨circleFullResolventH4 T h h₁ h₂ p hp hK v, ?_, ?_⟩
    · intro hu
      have hu' : circleFullResolventH4 T h h₁ h₂ p hp hK v = 0 := Subtype.ext hu
      have hi := circle_full_resolvent_right_inverse T h h₁ h₂ p hp hK v
      rw [hu', map_zero] at hi
      exact hvne hi.symm
    · rw [circle_complex_shift_resolvent]
      change (1-F) v = 0
      simp only [sub_apply, one_apply_eq_self, hfv, sub_self]
  · right
    have hunit : IsUnit (1-F) := by
      simpa only [spectrum.mem_resolventSet_iff, map_one] using hr
    obtain ⟨U, hU⟩ := hunit
    exact circle_complex_inverse_of_unit T h h₁ h₂ p hp hK z U hU

/-- Every spectral point of this unbounded H4-domain operator is an eigenvalue. -/
theorem circle_spectrum_iff_eigenvector (h h₁ h₂ : C(AddCircle T, ℂ)) (z : ℂ) :
    z ∈ circleSpectrum T h h₁ h₂ ↔
      ∃ u : circleH4Domain T, (u : CircleL2 T) ≠ 0 ∧
        circleH4Operator T h h₁ h₂ u = z • (u : CircleL2 T) := by
  constructor
  · intro hz
    rcases circle_complex_shift_alternative T h h₁ h₂ z with he | hr
    · obtain ⟨u, hune, hu⟩ := he
      refine ⟨u, hune, ?_⟩
      change z • (u : CircleL2 T)-circleH4Operator T h h₁ h₂ u = 0 at hu
      exact (sub_eq_zero.mp hu).symm
    · obtain ⟨R, _, hR⟩ := hr
      exact False.elim (hz ⟨R, hR⟩)
  · rintro ⟨u, hune, hu⟩ ⟨R, hR⟩
    have hi := hR.2 u
    have hs : circleComplexShift T h h₁ h₂ z u = 0 := by
      change z • (u : CircleL2 T)-circleH4Operator T h h₁ h₂ u = 0
      rw [hu, sub_self]
    rw [hs, map_zero] at hi
    exact hune hi.symm

end Lemniscate
