import Lemniscate.PeriodicResolventPerturbation
import Lemniscate.PeriodicPrincipalCompact
import Mathlib.Analysis.Normed.Ring.Units

/-! A compact bounded two-sided inverse of the full variable-coefficient
operator at an explicit positive real parameter. The domain is the actual
weak H4 domain, not a finite-dimensional approximation. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleNeumannInverse (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) :
    CircleL2 T →L[ℂ] CircleL2 T :=
  (Units.oneSub (circleLowerResolvent T h h₁ h₂ p hp) hK).inv

theorem circle_neumann_right_inverse (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) (f : CircleL2 T) :
    (1-circleLowerResolvent T h h₁ h₂ p hp)
      (circleNeumannInverse T h h₁ h₂ p hp hK f) = f := by
  have hu := (Units.oneSub (circleLowerResolvent T h h₁ h₂ p hp) hK).val_inv
  change (1-circleLowerResolvent T h h₁ h₂ p hp) *
    circleNeumannInverse T h h₁ h₂ p hp hK = 1 at hu
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using
    congrArg (fun L : CircleL2 T →L[ℂ] CircleL2 T => L f) hu

theorem circle_neumann_left_inverse (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) (f : CircleL2 T) :
    circleNeumannInverse T h h₁ h₂ p hp hK
      ((1-circleLowerResolvent T h h₁ h₂ p hp) f) = f := by
  have hu := (Units.oneSub (circleLowerResolvent T h h₁ h₂ p hp) hK).inv_val
  change circleNeumannInverse T h h₁ h₂ p hp hK *
    (1-circleLowerResolvent T h h₁ h₂ p hp) = 1 at hu
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using
    congrArg (fun L : CircleL2 T →L[ℂ] CircleL2 T => L f) hu

noncomputable def circleFullResolvent (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) :
    CircleL2 T →L[ℂ] CircleL2 T :=
  (circlePrincipalResolvent T (p^2) (by nlinarith)).comp
    (circleNeumannInverse T h h₁ h₂ p hp hK)

theorem circle_full_resolvent_mem_h4 (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) (f : CircleL2 T) :
    InCircleH4 T (circleFullResolvent T h h₁ h₂ p hp hK f) := by
  unfold circleFullResolvent
  simp only [ContinuousLinearMap.comp_apply]
  exact circle_principal_resolvent_mem_h4 T (p^2) (by nlinarith)
    (circleNeumannInverse T h h₁ h₂ p hp hK f)

noncomputable def circleFullResolventH4 (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) (f : CircleL2 T) :
    circleH4Domain T :=
  circlePrincipalResolventH4 T (p^2) (by nlinarith)
    (circleNeumannInverse T h h₁ h₂ p hp hK f)

theorem circle_full_resolvent_right_inverse (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) (f : CircleL2 T) :
    circleFullShift T h h₁ h₂ (p^2) (circleFullResolventH4 T h h₁ h₂ p hp hK f) = f := by
  unfold circleFullResolventH4
  rw [circle_full_shift_principal T h h₁ h₂ p hp]
  simpa only [sub_apply, one_apply_eq_self] using
    circle_neumann_right_inverse T h h₁ h₂ p hp hK f

theorem circle_full_resolvent_left_inverse (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) (f : circleH4Domain T) :
    circleFullResolvent T h h₁ h₂ p hp hK (circleFullShift T h h₁ h₂ (p^2) f) =
      (f : CircleL2 T) := by
  unfold circleFullResolvent
  simp only [ContinuousLinearMap.comp_apply]
  rw [circle_full_shift_factorization T h h₁ h₂ p hp,
    circle_neumann_left_inverse, circle_principal_resolvent_left_inverse]

theorem circle_full_resolvent_compact (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) :
    IsCompactOperator (circleFullResolvent T h h₁ h₂ p hp hK) := by
  have hr : 0 < p^2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hp)
  change IsCompactOperator
    ((circlePrincipalResolvent T (p^2) hr : CircleL2 T → CircleL2 T) ∘
      (circleNeumannInverse T h h₁ h₂ p hp hK : CircleL2 T → CircleL2 T))
  exact IsCompactOperator.comp_clm
    (f := (circlePrincipalResolvent T (p^2) hr : CircleL2 T → CircleL2 T))
    (circle_principal_resolvent_compact T (p^2) hr)
    (circleNeumannInverse T h h₁ h₂ p hp hK)

theorem circle_full_shift_bijective (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) :
    Function.Bijective (circleFullShift T h h₁ h₂ (p^2)) := by
  constructor
  · intro f g hfg
    apply Subtype.ext
    rw [← circle_full_resolvent_left_inverse T h h₁ h₂ p hp hK f,
      ← circle_full_resolvent_left_inverse T h h₁ h₂ p hp hK g, hfg]
  · intro f
    exact ⟨circleFullResolventH4 T h h₁ h₂ p hp hK f,
      circle_full_resolvent_right_inverse T h h₁ h₂ p hp hK f⟩

/-- Every continuous coefficient triple admits a compact bounded inverse at
some positive real parameter, with both inverse identities on the full domain. -/
theorem circle_full_compact_resolvent_exists (h h₁ h₂ : C(AddCircle T, ℂ)) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : CircleL2 T →L[ℂ] CircleL2 T,
      IsCompactOperator R ∧
      (∀ f : CircleL2 T, ∃ u : circleH4Domain T,
        (u : CircleL2 T) = R f ∧ circleFullShift T h h₁ h₂ r u = f) ∧
      (∀ u : circleH4Domain T, R (circleFullShift T h h₁ h₂ r u) = (u : CircleL2 T)) := by
  let p := circleResolventScale T h h₁ h₂
  have hp : 1 ≤ p := circle_resolvent_scale_ge_one T h h₁ h₂
  have hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1 :=
    circle_lower_resolvent_norm_lt_one T h h₁ h₂
  refine ⟨p^2, by nlinarith, circleFullResolvent T h h₁ h₂ p hp hK,
    circle_full_resolvent_compact T h h₁ h₂ p hp hK, ?_,
    circle_full_resolvent_left_inverse T h h₁ h₂ p hp hK⟩
  intro f
  exact ⟨circleFullResolventH4 T h h₁ h₂ p hp hK f, rfl,
    circle_full_resolvent_right_inverse T h h₁ h₂ p hp hK f⟩

end Lemniscate
