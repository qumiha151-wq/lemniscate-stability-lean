import SolitonClassification.Rotating.ResetMetricCell
import SolitonClassification.Rotating.ReferenceInversePerturbation

namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- Finite rational inverse checks are needed only at the left endpoint of
each polynomial. A global differential residual and the true coefficient
bound extend its invertibility through every point in that cell. -/
theorem inverse_on_cell {M dM A : ℝ→FlowEnd}
    (der : ∀t∈unitCell,HasDerivWithinAt M (dM t) unitCell t)
    (coef : ∀t∈unitCell,‖A t‖≤4/25)
    (res : ∀t∈unitCell,‖dM t-A t*M t‖≤6*eps)
    (u0 : IsUnit (M 0)) (m0 : ‖M 0‖≤2900) (i0 : ‖Ring.inverse (M 0)‖≤3500) :
    ∀t∈unitCell,IsUnit (M t) ∧ ‖M t‖≤5000 ∧ ‖Ring.inverse (M t)‖≤5000 := by
  let W := Ring.inverse (M 0)
  let B := fun t=>M t*W-1
  let dB := fun t=>dM t*W
  have z : B 0=0 := by dsimp [B,W];rw [Ring.mul_inverse_cancel _ u0,sub_self]
  have derB (t : ℝ) (ht : t∈unitCell) : HasDerivWithinAt B (dB t) unitCell t := by
    simpa [B,dB] using (((der t ht).mul_const W).sub_const 1)
  have con : ContinuousOn (fun t=>‖B t‖) unitCell :=
    (show ContinuousOn B unitCell from fun t ht=>(derB t ht).continuousWithinAt).norm
  obtain ⟨v,hv,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) con
  let K := (4/25)*(‖B v‖+1)+6*eps*3500
  have kpos : 0≤K := by unfold K eps; positivity
  have dbd (t : ℝ) (ht : t∈unitCell) : ‖dB t‖≤K := by
    have top : ‖B t‖≤‖B v‖ := hmax ht
    have tr : ‖M t*W‖≤‖B v‖+1 := by
      have n := norm_le_norm_sub_add (M t*W) (1:FlowEnd)
      simpa only [B,norm_one] using n.trans (add_le_add_left top _)
    have eq : dB t=A t*(M t*W)+(dM t-A t*M t)*W := by
      simp only [dB,sub_mul,mul_assoc];abel
    rw [eq]
    exact (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans
      (mul_le_mul (coef t ht) tr (norm_nonneg _) (by norm_num))) ((norm_mul_le ..).trans
      (mul_le_mul (res t ht) i0 (norm_nonneg _) (by norm_num [eps]))))
  have bnd := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    derB dbd (x:=0) (y:=v) (by norm_num [unitCell]) hv
  rw [z,sub_zero,sub_zero,Real.norm_eq_abs,abs_of_nonneg hv.1] at bnd
  have cv := bnd.trans ((mul_le_mul_of_nonneg_left hv.2 kpos).trans_eq (mul_one K))
  have maxB : ‖B v‖≤1/5 := by
    dsimp [K,eps] at cv
    linarith only [cv]
  intro t ht
  have hrel : ‖M t*W-1‖≤1/5 := (show ‖B t‖≤‖B v‖ from hmax ht).trans maxB
  obtain ⟨prodU,prodI⟩ := flowEnd_inverse_bound_one_fifth _ hrel
  have factor : (M t*W)*M 0=M t := by
    rw [mul_assoc,Ring.inverse_mul_cancel _ u0,mul_one]
  have unit := prodU.mul u0
  rw [factor] at unit
  have prodM : ‖M t*W‖≤6/5 := by
    have b := norm_le_norm_sub_add (M t*W) (1:FlowEnd)
    rw [norm_one] at b
    linarith only [b,hrel]
  refine ⟨unit,?_,?_⟩
  · calc
      ‖M t‖ = ‖(M t*W)*M 0‖ := congrArg norm factor.symm
      _ ≤ _ := (norm_mul_le ..).trans ((mul_le_mul prodM m0 (norm_nonneg _) (by norm_num)).trans (by norm_num))
  · calc
      ‖Ring.inverse (M t)‖ = ‖Ring.inverse ((M t*W)*M 0)‖ := congrArg (norm ∘ Ring.inverse) factor.symm
      _ = ‖W*Ring.inverse (M t*W)‖ := by rw [Ring.inverse_mul (Or.inl prodU)]
      _ ≤ _ := (norm_mul_le ..).trans ((mul_le_mul i0 prodI (norm_nonneg _) (by norm_num)).trans (by norm_num))
end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.inverse_on_cell
