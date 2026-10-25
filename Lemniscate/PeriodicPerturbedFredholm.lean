import Lemniscate.PeriodicFredholmAlternative

/-! A bounded L2 perturbation of the actual H4 operator has a compact inverse
whenever its kernel vanishes. This will be applied to the neutral rank-one
perturbation to construct the exact adjoint zero vector. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circlePerturbedShift (h h₁ h₂ : C(AddCircle T, ℂ)) (z : ℂ)
    (K : CircleL2 T →L[ℂ] CircleL2 T) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  circleComplexShift T h h₁ h₂ z + K.toLinearMap.comp (circleH4Domain T).subtype

noncomputable def circlePerturbedFeedback (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (hR : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1)
    (z : ℂ) (K : CircleL2 T →L[ℂ] CircleL2 T) : CircleL2 T →L[ℂ] CircleL2 T :=
  circleResolventFeedback T h h₁ h₂ p hp hR z - K.comp (circleFullResolvent T h h₁ h₂ p hp hR)

theorem circle_perturbed_feedback_compact (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (hR : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1)
    (z : ℂ) (K : CircleL2 T →L[ℂ] CircleL2 T) :
    IsCompactOperator (circlePerturbedFeedback T h h₁ h₂ p hp hR z K) := by
  apply (circle_resolvent_feedback_compact T h h₁ h₂ p hp hR z).sub
  exact (circle_full_resolvent_compact T h h₁ h₂ p hp hR).clm_comp K

theorem circle_perturbed_shift_resolvent (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (hR : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1)
    (z : ℂ) (K : CircleL2 T →L[ℂ] CircleL2 T) (f : CircleL2 T) :
    circlePerturbedShift T h h₁ h₂ z K (circleFullResolventH4 T h h₁ h₂ p hp hR f) =
      (1-circlePerturbedFeedback T h h₁ h₂ p hp hR z K) f := by
  change circleComplexShift T h h₁ h₂ z (circleFullResolventH4 T h h₁ h₂ p hp hR f) +
    K (circleFullResolvent T h h₁ h₂ p hp hR f) = _
  rw [circle_complex_shift_resolvent]
  simp only [circlePerturbedFeedback, sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]
  abel

theorem circle_perturbed_shift_factorization (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (hR : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1)
    (z : ℂ) (K : CircleL2 T →L[ℂ] CircleL2 T) (u : circleH4Domain T) :
    circlePerturbedShift T h h₁ h₂ z K u =
      (1-circlePerturbedFeedback T h h₁ h₂ p hp hR z K)
        (circleFullShift T h h₁ h₂ (p^2) u) := by
  have he := circle_perturbed_shift_resolvent T h h₁ h₂ p hp hR z K
    (circleFullShift T h h₁ h₂ (p^2) u)
  rw [circle_full_resolvent_h4_left_inverse] at he
  exact he

def CirclePerturbedInverseIdentities (h h₁ h₂ : C(AddCircle T, ℂ)) (z : ℂ)
    (K R : CircleL2 T →L[ℂ] CircleL2 T) : Prop :=
  (∀ f : CircleL2 T, ∃ u : circleH4Domain T,
    (u : CircleL2 T) = R f ∧ circlePerturbedShift T h h₁ h₂ z K u = f) ∧
  (∀ u : circleH4Domain T, R (circlePerturbedShift T h h₁ h₂ z K u) = (u : CircleL2 T))

theorem circle_perturbed_inverse_of_kernel (h h₁ h₂ : C(AddCircle T, ℂ)) (z : ℂ)
    (K : CircleL2 T →L[ℂ] CircleL2 T)
    (hinj : ∀ u : circleH4Domain T, circlePerturbedShift T h h₁ h₂ z K u = 0 →
      (u : CircleL2 T) = 0) :
    ∃ R : CircleL2 T →L[ℂ] CircleL2 T,
      IsCompactOperator R ∧ CirclePerturbedInverseIdentities T h h₁ h₂ z K R := by
  let p := circleResolventScale T h h₁ h₂
  have hp : 1 ≤ p := circle_resolvent_scale_ge_one T h h₁ h₂
  have hR : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1 :=
    circle_lower_resolvent_norm_lt_one T h h₁ h₂
  let F := circlePerturbedFeedback T h h₁ h₂ p hp hR z K
  have hF : IsCompactOperator F := circle_perturbed_feedback_compact T h h₁ h₂ p hp hR z K
  have hunit : IsUnit (1-F) := by
    rcases hF.hasEigenvalue_or_mem_resolventSet (by norm_num : (1:ℂ) ≠ 0) with he | hr
    · obtain ⟨v, hv⟩ := he.exists_hasEigenvector
      have hfv : F v = v := by
        have heq := hv.apply_eq_smul
        change F v = (1:ℂ) • v at heq
        simpa only [one_smul] using heq
      have hz : circlePerturbedShift T h h₁ h₂ z K
          (circleFullResolventH4 T h h₁ h₂ p hp hR v) = 0 := by
        rw [circle_perturbed_shift_resolvent]
        change (1-F) v = 0
        simp only [sub_apply, one_apply_eq_self, hfv, sub_self]
      have hu : circleFullResolventH4 T h h₁ h₂ p hp hR v = 0 :=
        Subtype.ext (hinj _ hz)
      have hi := circle_full_resolvent_right_inverse T h h₁ h₂ p hp hR v
      rw [hu, map_zero] at hi
      exact False.elim (hv.2 hi.symm)
    · simpa only [spectrum.mem_resolventSet_iff, map_one] using hr
  obtain ⟨U, hU⟩ := hunit
  let Q : CircleL2 T →L[ℂ] CircleL2 T := ↑U⁻¹
  have hright (f : CircleL2 T) : (U : CircleL2 T →L[ℂ] CircleL2 T) (Q f) = f := by
    simpa only [mul_apply_eq_comp, one_apply_eq_self, Q] using
      congrArg (fun L : CircleL2 T →L[ℂ] CircleL2 T => L f) (Units.mul_inv U)
  have hleft (f : CircleL2 T) : Q ((U : CircleL2 T →L[ℂ] CircleL2 T) f) = f := by
    simpa only [mul_apply_eq_comp, one_apply_eq_self, Q] using
      congrArg (fun L : CircleL2 T →L[ℂ] CircleL2 T => L f) (Units.inv_mul U)
  refine ⟨(circleFullResolvent T h h₁ h₂ p hp hR).comp Q, ?_, ?_⟩
  · change IsCompactOperator
      ((circleFullResolvent T h h₁ h₂ p hp hR : CircleL2 T → CircleL2 T) ∘ Q)
    exact IsCompactOperator.comp_clm
      (f := (circleFullResolvent T h h₁ h₂ p hp hR : CircleL2 T → CircleL2 T))
      (circle_full_resolvent_compact T h h₁ h₂ p hp hR) Q
  · constructor
    · intro f
      refine ⟨circleFullResolventH4 T h h₁ h₂ p hp hR (Q f), rfl, ?_⟩
      rw [circle_perturbed_shift_resolvent, ← hU]
      exact hright f
    · intro u
      simp only [ContinuousLinearMap.comp_apply]
      rw [circle_perturbed_shift_factorization T h h₁ h₂ p hp hR z K u, ← hU,
        hleft, circle_full_resolvent_left_inverse]

end Lemniscate
