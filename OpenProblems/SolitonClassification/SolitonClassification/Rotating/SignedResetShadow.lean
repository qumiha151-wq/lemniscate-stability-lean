import SolitonClassification.Rotating.ResetShadow
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set Metric Filter ODE
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
theorem signed_shadow_cell {s : ℝ} (hs : |s|≤1/100) {a da : ℝ→Aug} (ad : ∀t,HasDerivAt a (da t) t) (cd : Continuous da)
    (valid : ∀t∈Icc 0 1,Inner (a t) ∧ ‖da t-s • augmented (a t)‖≤eps)
    (e₀ : Aug) (initial : ‖e₀‖≤1/4) :
    ∃x : ℝ→Aug, x 0=a 0+e₀ ∧
      (∀t∈Icc 0 1,HasDerivWithinAt x (s • augmented (x t)) (Icc 0 1) t) ∧
      ∀t∈Icc 0 1,‖x t-a t‖≤3*‖e₀‖+2*eps := by
  let v := fun t e=>s • augmented (a t+e)-da t
  let t₀ : Icc (0:ℝ) 1 := ⟨0,by norm_num⟩
  have ca : Continuous a := continuous_iff_continuousAt.mpr fun t => (ad t).continuousAt
  have lip (t : ℝ) (ht : t∈Icc 0 1) {x y : Aug} (hx : ‖x‖≤1) (hy : ‖y‖≤1) :
      ‖v t x-v t y‖≤(2/5)*‖x-y‖ := by
    have g := augmented_lipschitz (a t+x) (a t+y) (shift_in_box (valid t ht).1 hx) (shift_in_box (valid t ht).1 hy)
    rw [add_sub_add_left_eq_sub] at g
    change ‖(s • _-da t)-(s • _-da t)‖≤_
    rw [sub_sub_sub_cancel_right,←smul_sub,norm_smul,Real.norm_eq_abs]
    have hh : |s| *40≤2/5 := by linarith only [hs]
    exact (mul_le_mul_of_nonneg_left g (abs_nonneg s)).trans
      (by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right hh (norm_nonneg _))
  have rhs (t : ℝ) (ht : t∈Icc 0 1) (e : Aug) (he : ‖e‖≤1) : ‖v t e‖≤(2/5)*‖e‖+eps := by
    have d := lip t ht he (y:=0) (by norm_num)
    rw [sub_zero] at d
    have st : ‖v t 0‖≤eps := by
      dsimp only [v]; rw [add_zero,norm_sub_rev]; exact (valid t ht).2
    exact (norm_le_norm_sub_add _ _).trans (add_le_add d st)
  have hp : IsPicardLindelof v t₀ (0:Aug) 1 (1/4) (1/2) 1 := by
    constructor
    · intro t ht
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro x hx y hy
      have d := lip t ht (mem_closedBall_zero_iff.mp hx) (mem_closedBall_zero_iff.mp hy)
      change _≤(1:ℝ)*‖x-y‖
      nlinarith only [d,norm_nonneg (x-y)]
    · intro x _
      change ContinuousOn (fun t => s • augmented (a t+x)-da t) _
      exact (((aug_cont.comp (ca.add (continuous_const (y:=x)))).const_smul s).sub cd).continuousOn
    · intro t ht x hx
      have ex := rhs t ht x (mem_closedBall_zero_iff.mp hx)
      change ‖v t x‖≤(↑(1/2:ℝ≥0):ℝ)
      rw [NNReal.coe_div]
      norm_num only [NNReal.coe_one,NNReal.coe_ofNat]
      dsimp [eps] at ex
      have b : ‖x‖≤1 := mem_closedBall_zero_iff.mp hx
      linarith only [b,ex]
    · norm_num [t₀]
  have ein : e₀∈closedBall (0:Aug) (↑(1/4:ℝ≥0):ℝ) := by
    apply mem_closedBall_zero_iff.mpr
    simpa using initial
  obtain ⟨z,hz⟩ := FunSpace.exists_isFixedPt_next hp ein
  let e := z.compProj
  have e0 : e 0=e₀ := by
    change z.compProj (t₀:ℝ)=e₀
    rw [FunSpace.compProj_val,←hz,FunSpace.next_apply₀]
  have ball (t : ℝ) : ‖e t‖≤1 := mem_closedBall_zero_iff.mp (z.compProj_mem_closedBall hp.mul_max_le)
  have de (t : ℝ) (ht : t∈Icc 0 1) : HasDerivWithinAt e (v t (e t)) (Icc 0 1) t := by
    apply hasDerivWithinAt_picard_Icc t₀.2 hp.continuousOn_uncurry z.continuous_compProj.continuousOn
      (fun _ _ => z.compProj_mem_closedBall hp.mul_max_le) e₀ ht |>.congr_of_mem _ ht
    intro t' ht'
    dsimp only [e]
    nth_rw 1 [←hz]
    rw [FunSpace.compProj_of_mem ht',FunSpace.next_apply]
  refine ⟨fun t=>a t+e t,by change a 0+e 0=a 0+e₀; rw [e0],?_,?_⟩
  · intro t ht
    apply ((ad t).hasDerivWithinAt.add (de t ht)).congr_deriv
    dsimp only [v]; abel
  · have rightD (t : ℝ) (ht : t∈Ico 0 1) : HasDerivWithinAt e (v t (e t)) (Ici t) t := by
      apply (de t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      exact mem_of_superset (Icc_mem_nhdsGE ht.2) (fun _ hs=>⟨ht.1.trans hs.1,hs.2⟩)
    have diff (t : ℝ) (ht : t∈Ico 0 1) : ‖v t (e t)‖≤1*‖e t‖+eps := by
      have d := rhs t (Ico_subset_Icc_self ht) (e t) (ball t)
      linarith only [d,norm_nonneg (e t)]
    have b := norm_le_gronwallBound_of_norm_deriv_right_le z.continuous_compProj.continuousOn rightD
      (show ‖e 0‖≤‖e₀‖ by rw [e0]) diff
    intro t ht
    rw [add_sub_cancel_left]
    refine (b t ht).trans ?_
    simp only [gronwallBound,one_ne_zero,if_false,sub_zero,one_mul,div_one]
    have hex := Real.abs_exp_sub_one_le (show |t|≤1 by rw [abs_of_nonneg ht.1];exact ht.2)
    rw [abs_of_nonneg ht.1] at hex
    have exp : Real.exp t≤3 := by linarith [le_abs_self (Real.exp t-1),ht.2]
    have ep : 0≤eps := by norm_num [eps]
    nlinarith only [mul_le_mul_of_nonneg_left exp (norm_nonneg e₀),mul_le_mul_of_nonneg_left exp ep]

end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.signed_shadow_cell
