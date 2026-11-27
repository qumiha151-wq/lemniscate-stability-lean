import SolitonClassification.Rotating.ResetDependence
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set Metric ODE
open scoped NNReal
set_option backward.isDefEq.respectTransparency false

theorem true_speed {x : State} (hx : StateBox x) : ‖field x‖≤110 := by
  have h0:=hx 0 (by decide);have h1:=hx 1 (by decide)
  have h2:=hx 2 (by decide);have h3:=hx 3 (by decide);have h4:=hx 4 (by decide)
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i;rw [Real.norm_eq_abs];fin_cases i
  · change |8*x 1|≤_;rw [abs_mul];norm_num;linarith
  · change |-(x 0)^3/16-x 2/8-x 4*x 3/8|≤_
    calc
      _ ≤ |-(x 0)^3/16-x 2/8|+|x 4*x 3/8| := abs_sub _ _
      _ ≤ (|-(x 0)^3/16|+|x 2/8|)+|x 4*x 3/8| := by gcongr;exact abs_sub _ _
      _ = |x 0|^3/16+|x 2|/8+|x 4| *|x 3|/8 := by simp [abs_div,abs_pow,abs_mul]
      _ ≤ 10^3/16+10/8+10*10/8 := by gcongr
      _ ≤ _ := by norm_num
  · change |-x 0*x 3|≤_;rw [abs_mul,abs_neg];exact (mul_le_mul h0 h3 (abs_nonneg _) (by norm_num)).trans (by norm_num)
  · change |1+x 0*x 2|≤_
    have z := abs_add_le (1:ℝ) (x 0*x 2)
    rw [abs_one,abs_mul] at z
    exact z.trans ((add_le_add_right (mul_le_mul h0 h2 (abs_nonneg _) (by norm_num)) 1).trans (by norm_num))
  · norm_num [field]
  · change |x 0|≤_;linarith

theorem short_state {τ : ℝ} (htau : |τ|≤1/10^30) (a : State)
    (margin : ∀i : Fin 6,i.val<5→|a i|≤19/2) :
    ∃x : ℝ→State,x 0=a ∧ FollowsState τ x ∧
      (∀t∈unitCell,StateBox (x t)) ∧ ∀t∈unitCell,‖x t-a‖≤110*|τ| := by
  let t₀ : unitCell := ⟨0,by norm_num [unitCell]⟩
  let f := fun (_:ℝ) e=>τ • field (a+e)
  have inbox (e : State) (he : e∈closedBall (0:State) (1/2)) : StateBox (a+e) := by
    intro i hi
    have de := (coordinate_bound e i).trans (mem_closedBall_zero_iff.mp he)
    exact (abs_add_le ..).trans ((add_le_add (margin i hi) de).trans (by norm_num))
  have rhs (e : State) (he : e∈closedBall (0:State) (1/2)) : ‖τ • field (a+e)‖≤110*|τ| := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (true_speed (inbox e he)) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hp : IsPicardLindelof f t₀ (0:State) (1/2) 0 (1/4) 1 := by
    constructor
    · intro t ht
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro e he g hg
      have dif := field_wide_lip (inbox e (by simpa using he)) (inbox g (by simpa using hg))
      rw [add_sub_add_left_eq_sub] at dif
      change ‖τ • field (a+e)-τ • field (a+g)‖≤(1:ℝ)*‖e-g‖
      rw [←smul_sub,norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul htau dif (norm_nonneg _) (by norm_num)).trans (by
        rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))
    · intro _ _;exact continuousOn_const
    · intro t ht e he
      have z:=rhs e (by simpa using he)
      change ‖τ • field (a+e)‖≤(↑(1/4:ℝ≥0):ℝ)
      norm_num only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
      linarith only [htau,z]
    · norm_num [t₀]
  obtain ⟨z,hz⟩ := FunSpace.exists_isFixedPt_next hp (x:=(0:State)) (by simp)
  let e := z.compProj
  have at0 : e 0=0 := by
    change z.compProj (t₀:ℝ)=0;rw [FunSpace.compProj_val,←hz,FunSpace.next_apply₀]
  have ball (t : ℝ) : e t∈closedBall (0:State) (1/2:ℝ) := by simpa [e] using z.compProj_mem_closedBall hp.mul_max_le (t:=t)
  have de (t : ℝ) (ht : t∈unitCell) : HasDerivWithinAt e (τ • field (a+e t)) unitCell t := by
    apply hasDerivWithinAt_picard_Icc t₀.2 hp.continuousOn_uncurry z.continuous_compProj.continuousOn
      (fun _ _ => z.compProj_mem_closedBall hp.mul_max_le) (0:State) ht |>.congr_of_mem _ ht
    intro t' ht'; dsimp only [e];nth_rw 1 [←hz];rw [FunSpace.compProj_of_mem ht',FunSpace.next_apply]
  refine ⟨fun t=>a+e t,by change a+e 0=a;rw [at0,add_zero],?_,fun t _=>inbox (e t) (ball t),?_⟩
  · intro t ht
    exact (de t ht).const_add a
  · intro t ht
    have m := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le de
      (fun t _=>rhs (e t) (ball t)) t₀.2 ht
    change ‖e t-e 0‖≤110*|τ| *‖t-0‖ at m
    rw [at0,sub_zero,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] at m
    simpa only [add_sub_cancel_left] using m.trans ((mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans_eq (mul_one _))

theorem short_state_and_matrix {τ : ℝ} (htau : |τ|≤1/10^30) (a : State)
    (margin : ∀i : Fin 6,i.val<5→|a i|≤19/2) (J₀ : FlowEnd) (normJ : ‖J₀‖≤5001) :
    ∃x : ℝ→State, ∃J : ℝ→FlowEnd,x 0=a ∧ J 0=J₀ ∧ FollowsState τ x ∧
      (∀t∈unitCell,HasDerivWithinAt J (actualCoefficient τ x t*J t) unitCell t) ∧
      ∀t∈unitCell,‖x t-a‖≤110*|τ| ∧ ‖J t-J₀‖≤400080*|τ| := by
  obtain ⟨x,ini,xd,box,bd⟩:=short_state htau a margin
  have xc : ContinuousOn x unitCell := fun t ht=>(xd t ht).continuousWithinAt
  have ha : ContinuousOn (actualCoefficient τ x) unitCell :=
    (field_fderiv_differentiable.continuous.comp_continuousOn xc).const_smul τ
  have Hnorm (t : ℝ) (ht : t∈unitCell) : ‖actualCoefficient τ x t‖≤40*|τ| := by
    have deriv : ‖fderiv ℝ field (x t)‖≤40 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro v;rw [field_fderiv_apply];exact linear_ten (box t ht) v
    rw [actualCoefficient,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left deriv (abs_nonneg _)).trans_eq (mul_comm _ _)
  obtain ⟨u,u0,ud,du⟩ := linear_step ha (by linarith only [htau] : 40*|τ|≤1/8) Hnorm 1 (by norm_num)
  refine ⟨x,fun t=>u t*J₀,ini,by change u 0*J₀=J₀;rw [u0,one_mul],xd,?_,?_⟩
  · intro t ht
    simpa only [mul_assoc] using (ud t ht).mul_const J₀
  · intro t ht; refine ⟨bd t ht,?_⟩
    change ‖u t*J₀-J₀‖≤_
    rw [show u t*J₀-J₀=(u t-1)*J₀ by rw [sub_mul,one_mul]]
    exact (norm_mul_le ..).trans ((mul_le_mul (du t ht) normJ (norm_nonneg _) (by positivity)).trans_eq (by ring))
end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.short_state_and_matrix
