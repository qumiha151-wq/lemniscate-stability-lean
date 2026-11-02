import Lemniscate.PeriodicAuxiliaryHighAction
import Lemniscate.FiniteHeadInputIntervals

/-! Ordinary L2 bounds for the actual finite changes of variables. These
replace unnecessary estimates in weighted projection spaces. -/
namespace Lemniscate.CoarseArithmetic
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_householder_den_at_least_one : 1 ≤ finiteHouseholderDenInput.lo := by
  decide +kernel
end Lemniscate.CoarseArithmetic

namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

private theorem householder_adjoint_domain_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {D : Submodule ℂ E} (e a f : D)
    (he : inner ℂ (e:E) (e:E) = 1) (ha : inner ℂ (a:E) (a:E) = 1)
    (hea : inner ℂ (a:E) (e:E) = inner ℂ (e:E) (a:E))
    (hd : 1+inner ℂ (e:E) (a:E) ≠ 0) :
    ‖neutralHouseholderAdjointDomain e a f‖ = ‖f‖ := by
  have hc : conj (1+inner ℂ (e:E) (a:E)) = 1+inner ℂ (e:E) (a:E) := by
    rw [map_add,map_one,inner_conj_symm,hea]
  change ‖f-(conj (1+inner ℂ (e:E) (a:E))⁻¹*inner ℂ ((e:E)+(a:E)) (f:E)) • (e+a)‖ = ‖f‖
  rw [map_inv₀,hc]
  change ‖(neutralHouseholderDomain e a f:E)‖ = ‖(f:E)‖
  rw [neutral_householder_domain_coe]
  exact neutral_householder_norm (e:E) (a:E) he ha hea hd (f:E)

variable (T : ℝ) [Fact (0 < T)]

theorem circle_finite_rotation_anchor_pairing :
    inner ℂ (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T) =
      ((∑ i : Fin 31, finiteRotationHead i*finiteAnchorHead i:ℝ):ℂ) := by
  rw [← circle_householder_anchor_h4_coe,circle_finite_rotation_phase_head,circle_anchor_head,
    circle_even_head_inner]
  simp only [Complex.conj_ofReal,Complex.ofReal_sum,Complex.ofReal_mul]
  rfl

theorem circle_finite_householder_hypotheses :
    inner ℂ (circleFiniteRotationPhase T:CircleL2 T) (circleFiniteRotationPhase T:CircleL2 T) = 1 ∧
    inner ℂ (circleHouseholderAnchor T) (circleFiniteRotationPhase T:CircleL2 T) =
      inner ℂ (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T) ∧
    1 ≤ ‖1+inner ℂ (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T)‖ := by
  have hreal : conj (inner ℂ (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T)) =
      inner ℂ (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T) := by
    rw [circle_finite_rotation_anchor_pairing,Complex.conj_ofReal]
  refine ⟨?_,?_,?_⟩
  · rw [inner_self_eq_norm_sq_to_K,(circle_finite_phase_normalization T).1]
    norm_num
  · simpa only [inner_conj_symm] using hreal
  · have hnum : (1:ℝ) ≤ (finiteHouseholderDenInput.lo:ℝ) := by
      have hc : ((1:ℚ):ℝ) ≤ (finiteHouseholderDenInput.lo:ℝ) :=
        Rat.cast_le.mpr finite_householder_den_at_least_one
      norm_num only [Rat.cast_one] at hc
      exact hc
    have hd := hnum.trans finite_householder_den_input_sound.1
    rw [circle_finite_rotation_anchor_pairing,← Complex.ofReal_one,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_eq_abs]
    exact hd.trans (le_abs_self _)

theorem circle_finite_change_l2_bounds :
    ‖(circleHouseholderAnchor T)‖ = 1 ∧
    ‖(circleFiniteAdjointPhaseH4 T-circleFiniteRotationPhase T:circleH4Domain T)‖ ≤ 1 ∧
    ‖(circleFiniteRotationPhase T:CircleL2 T)+circleHouseholderAnchor T‖ ≤ 2 ∧
    (∀ f : circleH4Domain T,
      ‖neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f‖ = ‖f‖ ∧
      ‖neutralHouseholderAdjointDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f‖ = ‖f‖) := by
  rcases circle_finite_householder_hypotheses T with ⟨he,hea,hden⟩
  have hd : 1+inner ℂ (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T) ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hden
    norm_num at hden
  have ha : ‖circleHouseholderAnchor T‖ = 1 := by
    have h := congrArg Complex.re (circle_householder_anchor_unit T)
    simp [inner_self_eq_norm_sq_to_K,pow_two] at h
    nlinarith only [h,norm_nonneg (circleHouseholderAnchor T)]
  refine ⟨ha,?_,?_,?_⟩
  · have h := (circle_finite_normalization_bounds T).2.2
    have h' : ‖((circleAdjointApproximation T-circleRotationApproximation T:circleH4Domain T):CircleL2 T)‖ ≤ 1 := by
      linarith only [h]
    change ‖((circleFiniteAdjointPhaseH4 T-circleFiniteRotationPhase T:circleH4Domain T):CircleL2 T)‖ ≤ 1
    simpa only [circleFiniteAdjointPhaseH4,circleFiniteRotationPhase,Submodule.coe_sub,
      Submodule.coe_smul_of_tower,← smul_sub,norm_smul,Complex.norm_I,one_mul] using h'
  · have h := norm_add_le (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T)
    rw [(circle_finite_phase_normalization T).1,ha] at h
    norm_num at h
    exact h
  · intro f
    have hnorm := neutral_householder_norm (circleFiniteRotationPhase T:CircleL2 T)
      (circleHouseholderAnchor T) he (circle_householder_anchor_unit T) hea hd (f:CircleL2 T)
    constructor
    · change ‖(neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f:CircleL2 T)‖ = ‖(f:CircleL2 T)‖
      rw [neutral_householder_domain_coe,circle_householder_anchor_h4_coe]
      exact hnorm
    · exact householder_adjoint_domain_norm (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
        f he (circle_householder_anchor_unit T) hea hd

end Lemniscate
