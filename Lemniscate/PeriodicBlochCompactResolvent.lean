import Lemniscate.PeriodicBlochResolventFactorization
import Lemniscate.PeriodicPrincipalCompact
import Mathlib.Analysis.Normed.Ring.Units

/-! A compact bounded inverse at one positive real parameter for the actual
Bloch operator, with its range and both inverse identities on the H4 domain. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

private theorem principal_compact_composition (r : ℝ) (hr : 0 < r)
    (Q : CircleL2 T →L[ℂ] CircleL2 T) :
    IsCompactOperator ((circlePrincipalResolvent T r hr).comp Q) := by
  change IsCompactOperator ((circlePrincipalResolvent T r hr : CircleL2 T → CircleL2 T) ∘ Q)
  exact IsCompactOperator.comp_clm
    (f := (circlePrincipalResolvent T r hr : CircleL2 T → CircleL2 T))
    (circle_principal_resolvent_compact T r hr) Q

private theorem principal_composition_range (r : ℝ) (hr : 0 < r)
    (Q : CircleL2 T →L[ℂ] CircleL2 T) (f : CircleL2 T) :
    (circlePrincipalResolventH4 T r hr (Q f):CircleL2 T) =
      ((circlePrincipalResolvent T r hr).comp Q) f := rfl

def CircleBlochInverseIdentities (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) (w : ℂ)
    (R : CircleL2 T →L[ℂ] CircleL2 T) : Prop :=
  (∀ f : CircleL2 T, ∃ u : circleH4Domain T,
    (u:CircleL2 T) = R f ∧ circleBlochComplexShift T h h₁ h₂ α w u = f) ∧
  (∀ u : circleH4Domain T, R (circleBlochComplexShift T h h₁ h₂ α w u) = (u:CircleL2 T))

set_option maxHeartbeats 1000000 in
private theorem bloch_compact_inverse_of_small_remainder (h h₁ h₂ : C(AddCircle T, ℂ))
    (α p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleBlochLowerResolvent T h h₁ h₂ α p hp‖ < 1) :
    ∃ R : CircleL2 T →L[ℂ] CircleL2 T,
      IsCompactOperator R ∧ CircleBlochInverseIdentities T h h₁ h₂ α (p^4:ℝ) R := by
  let K := circleBlochLowerResolvent T h h₁ h₂ α p hp
  have hunit : IsUnit (1-K) := (Units.oneSub K hK).isUnit
  obtain ⟨U,hU⟩ := hunit
  let Q : CircleL2 T →L[ℂ] CircleL2 T := ↑U⁻¹
  have hright (f : CircleL2 T) : (1-K) (Q f) = f := by
    rw [← hU]
    simpa only [mul_apply_eq_comp,one_apply_eq_self,Q] using
      congrArg (fun L : CircleL2 T →L[ℂ] CircleL2 T => L f) (Units.mul_inv U)
  have hleft (f : CircleL2 T) : Q ((1-K) f) = f := by
    rw [← hU]
    simpa only [mul_apply_eq_comp,one_apply_eq_self,Q] using
      congrArg (fun L : CircleL2 T →L[ℂ] CircleL2 T => L f) (Units.inv_mul U)
  let R := (circlePrincipalResolvent T (p^4) (by positivity)).comp Q
  have hcompact : IsCompactOperator R := principal_compact_composition T (p^4) (by positivity) Q
  refine ⟨R,hcompact,?_⟩
  constructor
  · intro f
    refine ⟨circlePrincipalResolventH4 T (p^4) (by positivity) (Q f),?_,?_⟩
    · exact principal_composition_range T (p^4) (by positivity) Q f
    · rw [circle_bloch_shift_principal T h h₁ h₂ α p hp]
      have hi := hright f
      simpa only [sub_apply,one_apply_eq_self] using hi
  · intro u
    simp only [R,ContinuousLinearMap.comp_apply]
    rw [circle_bloch_shift_factorization T h h₁ h₂ α p hp,hleft,circle_principal_resolvent_left_inverse]

theorem circle_bloch_compact_resolvent_exists (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : ‖h‖ ≤ 1) (hh₁ : ‖h₁‖ ≤ 2) (hh₂ : ‖h₂‖ ≤ 4)
    (α : ℝ) (hz : ‖(α:ℂ)*circleFrequencyFactor T 1‖ ≤ 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : CircleL2 T →L[ℂ] CircleL2 T,
      IsCompactOperator R ∧ CircleBlochInverseIdentities T h h₁ h₂ α (r:ℂ) R := by
  let p : ℝ := 2000
  have hp : 1 ≤ p := by norm_num [p]
  have hK : ‖circleBlochLowerResolvent T h h₁ h₂ α p hp‖ < 1 := by
    have h := circle_bloch_lower_resolvent_norm_le T h h₁ h₂ hh hh₁ hh₂ α p hp hz
    exact h.trans_lt (by norm_num [p])
  obtain ⟨R,hcompact,hR⟩ := bloch_compact_inverse_of_small_remainder T h h₁ h₂ α p hp hK
  exact ⟨p^4,by positivity,R,hcompact,hR⟩

end Lemniscate
