import SolitonClassification.Rotating.ResetTapeTransport
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set Metric ODE
open scoped NNReal
set_option backward.isDefEq.respectTransparency false

/-- The moving-frame linear ODE is solved on one full cell and incurs a
change proportional to the coefficient itself, even at a long-time reset. -/
theorem linear_step {H : ℝ→FlowEnd} (hc : ContinuousOn H unitCell) {δ : ℝ} (hδ : δ≤1/8)
    (bound : ∀t∈unitCell,‖H t‖≤δ) (v : FlowEnd) (ini : ‖v-1‖≤1/4) :
    ∃U : ℝ→FlowEnd, U 0=v ∧
      (∀t∈unitCell,HasDerivWithinAt U (H t*U t) unitCell t) ∧
      ∀t∈unitCell,‖U t-v‖≤2*δ := by
  let t₀ : unitCell := ⟨0,by norm_num [unitCell]⟩
  let f := fun t (u : FlowEnd)=>H t*u
  have around (w : FlowEnd) (hw : w∈closedBall (1:FlowEnd) (1:ℝ)) : ‖w‖≤2 := by
    have p : ‖w-1‖≤1 := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have b:=norm_le_norm_sub_add w (1:FlowEnd)
    rw [norm_one] at b
    linarith only [b,p]
  have hp : IsPicardLindelof f t₀ (1:FlowEnd) 1 (1/4) (1/2) 1 := by
    constructor
    · intro t ht
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro x hx y hy
      change ‖H t*x-H t*y‖≤(1:ℝ)*‖x-y‖
      rw [←mul_sub]
      exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((bound t ht).trans (hδ.trans (by norm_num))) (norm_nonneg _))
    · intro u _
      exact hc.mul continuousOn_const
    · intro t ht u hu
      have h := (norm_mul_le (H t) u).trans (mul_le_mul ((bound t ht).trans hδ) (around u hu) (norm_nonneg _) (by norm_num))
      change ‖H t*u‖≤(↑(1/2:ℝ≥0):ℝ)
      norm_num at h ⊢;linarith only [h]
    · norm_num [t₀]
  have mem : v∈closedBall (1:FlowEnd) (↑(1/4:ℝ≥0):ℝ) := by
    simpa [mem_closedBall,dist_eq_norm] using ini
  obtain ⟨z,hz⟩ := FunSpace.exists_isFixedPt_next hp mem
  let U := z.compProj
  have at0 : U 0=v := by
    change z.compProj (t₀:ℝ)=v
    rw [FunSpace.compProj_val,←hz,FunSpace.next_apply₀]
  have within (t : ℝ) : ‖U t‖≤2 := around _ (z.compProj_mem_closedBall hp.mul_max_le)
  have du (t : ℝ) (ht : t∈unitCell) : HasDerivWithinAt U (H t*U t) unitCell t := by
    apply hasDerivWithinAt_picard_Icc t₀.2 hp.continuousOn_uncurry z.continuous_compProj.continuousOn
      (fun _ _ => z.compProj_mem_closedBall hp.mul_max_le) v ht |>.congr_of_mem _ ht
    intro t' ht'
    dsimp only [U]
    nth_rw 1 [←hz]
    rw [FunSpace.compProj_of_mem ht',FunSpace.next_apply]
  have pos : 0≤δ := (norm_nonneg _).trans (bound 0 t₀.2)
  have val (t : ℝ) (ht : t∈unitCell) : ‖H t*U t‖≤2*δ :=
    (norm_mul_le ..).trans ((mul_le_mul (bound t ht) (within t) (norm_nonneg _) pos).trans_eq (mul_comm _ _))
  refine ⟨U,at0,du,?_⟩
  intro t ht
  have m := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le du val t₀.2 ht
  change ‖U t-U 0‖≤2*δ*‖t-0‖ at m
  rw [at0,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] at m
  exact m.trans ((mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans_eq (mul_one _))

theorem derivative_wide {a x : State} (ha : |a 0|≤9) (hx : ‖x-a‖≤1) :
    ‖fderiv ℝ field x-fderiv ℝ field a‖≤5*‖x-a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let u:=x-a
  have expansion := linear_line_expansion a u v 1
  simp only [one_smul,one_pow,u,add_sub_cancel] at expansion
  change ‖fderiv ℝ field x v-fderiv ℝ field a v‖≤_
  rw [field_fderiv_apply,field_fderiv_apply,expansion]
  rw [show linear a v+(bilinear a (x-a) v+bilinear a v (x-a))+
    (3:ℝ) • trilinear (x-a) (x-a) v-linear a v=
    (bilinear a (x-a) v+bilinear a v (x-a))+(3:ℝ) • trilinear (x-a) (x-a) v by abel]
  apply (norm_add_le ..).trans
  have z := (norm_add_le ..).trans (add_le_add (bilinear_wide ha (x-a) v) (bilinear_wide ha v (x-a)))
  have h3 := trilinear_bound (x-a) (x-a) v
  have sq := mul_le_mul_of_nonneg_right hx (mul_nonneg (norm_nonneg (x-a)) (norm_nonneg v))
  rw [norm_smul,Real.norm_eq_abs]
  norm_num
  nlinarith only [h3,z,sq,mul_nonneg (norm_nonneg (x-a)) (norm_nonneg v)]
end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.linear_step
