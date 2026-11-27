import SolitonClassification.Rotating.ResetTapeVariation
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
theorem bilinear_ten {a : State} (h0 : |a 0|≤10) (u v : State) :
    ‖bilinear a u v‖≤2*‖u‖*‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i <;> try { change ‖(0:ℝ)‖≤_; simp; positivity }
  · change |-3*a 0*u 0*v 0/16-u 4*v 3/8|≤_
    calc
      _ ≤ |-3*a 0*u 0*v 0/16|+|u 4*v 3/8| := abs_sub _ _
      _ = 3*|a 0| * |u 0| * |v 0|/16+|u 4| * |v 3|/8 := by
        simp only [abs_div,abs_mul]; norm_num
      _ ≤ 3*10*‖u‖*‖v‖/16+‖u‖*‖v‖/8 := by
        gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]
  · change |-u 0*v 3|≤_
    rw [abs_mul,abs_neg]
    calc
      _ ≤ ‖u‖*‖v‖ := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]
  · change |u 0*v 2|≤_
    rw [abs_mul]
    calc
      _ ≤ ‖u‖*‖v‖ := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]

theorem field_quadratic_ten {a x : State} (ha : |a 0|≤10)
    (hx : ‖x-a‖≤1) : ‖field x-field a-fderiv ℝ field a (x-a)‖≤3*‖x-a‖^2 := by
  have eq := field_expansion a (x-a)
  rw [add_sub_cancel] at eq
  have cancel : field x-field a-fderiv ℝ field a (x-a)=
      bilinear a (x-a) (x-a)+trilinear (x-a) (x-a) (x-a) := by
    rw [field_fderiv_apply,eq]; abel
  rw [cancel]
  apply (norm_add_le ..).trans
  have h1 := bilinear_ten ha (x-a) (x-a)
  have h2 := trilinear_bound (x-a) (x-a) (x-a)
  have h3 := mul_le_mul_of_nonneg_left hx (sq_nonneg ‖x-a‖)
  nlinarith only [h1,h2,h3,sq_nonneg ‖x-a‖]

theorem linear_ten {a : State} (ha : ∀i : Fin 6,i.val<5 → |a i|≤10) (u : State) :
    ‖linear a u‖≤40*‖u‖ := by
  have h0 := ha 0 (by decide)
  have h2 := ha 2 (by decide)
  have h3 := ha 3 (by decide)
  have h4 := ha 4 (by decide)
  have hn := norm_nonneg u
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · change |8*u 1|≤_
    rw [abs_mul]; norm_num
    linarith [coordinate_bound u 1]
  · change |-3*(a 0)^2*u 0/16-u 2/8-a 4*u 3/8-u 4*a 3/8|≤_
    calc
      _ ≤ |-3*(a 0)^2*u 0/16-u 2/8-a 4*u 3/8|+|u 4*a 3/8| := abs_sub _ _
      _ ≤ (|-3*(a 0)^2*u 0/16-u 2/8|+|a 4*u 3/8|)+|u 4*a 3/8| := by
        gcongr; apply abs_sub
      _ ≤ ((|-3*(a 0)^2*u 0/16|+|u 2/8|)+|a 4*u 3/8|)+|u 4*a 3/8| := by
        gcongr; apply abs_sub
      _ = 3*|a 0|^2*|u 0|/16+|u 2|/8+|a 4| * |u 3|/8+|u 4| * |a 3|/8 := by
        simp only [abs_div,abs_mul,abs_pow]; norm_num
      _ ≤ 3*10^2*‖u‖/16+‖u‖/8+10*‖u‖/8+‖u‖*10/8 := by
        gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith
  · change |-a 0*u 3-u 0*a 3|≤_
    calc
      _ ≤ |-a 0*u 3|+|u 0*a 3| := abs_sub _ _
      _ = |a 0| * |u 3|+|u 0| * |a 3| := by simp [abs_mul]
      _ ≤ 10*‖u‖+‖u‖*10 := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by linarith
  · change |a 0*u 2+u 0*a 2|≤_
    calc
      _ ≤ |a 0*u 2|+|u 0*a 2| := abs_add_le _ _
      _ = |a 0| * |u 2|+|u 0| * |a 2| := by simp [abs_mul]
      _ ≤ 10*‖u‖+‖u‖*10 := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by linarith
  · simp [linear]
  · change |u 0|≤_
    linarith [coordinate_bound u 0]

def StateBox (x : State) := ∀i : Fin 6,i.val<5 → |x i|≤10

theorem field_wide_lip {a b : State} (ha : StateBox a) (hb : StateBox b) :
    ‖field a-field b‖≤40*‖a-b‖ := by
  let u : Aug := (a,0)
  let v : Aug := (b,0)
  have U : Box u := ⟨ha,by intro j i;norm_num [u]⟩
  have V : Box v := ⟨hb,by intro j i;norm_num [v]⟩
  have h := (norm_fst_le (augmented u-augmented v)).trans (augmented_lipschitz u v U V)
  simpa only [u,v,augmented,Prod.fst_sub,Prod.snd_sub,Prod.norm_def,sub_self,norm_zero,
    max_eq_left (norm_nonneg _)] using h

theorem cell_differential_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f v : ℝ→E} {k : ℝ} (der : ∀t∈unitCell,HasDerivWithinAt f (v t) unitCell t)
    (bd : ∀t∈unitCell,‖v t‖≤(2/5)*‖f t‖+k) (kp : 0≤k) :
    ∀t∈unitCell,‖f t‖≤2*(‖f 0‖+k) := by
  have cf : ContinuousOn f unitCell := fun t ht=>(der t ht).continuousWithinAt
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) cf.norm
  have vel (t : ℝ) (ht : t∈unitCell) : ‖v t‖≤(2/5)*‖f m‖+k := (bd t ht).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left (hmax ht) (by norm_num)) k)
  have maxStep := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le der vel
    (x:=0) (y:=m) (by norm_num [unitCell]) hm
  rw [sub_zero,Real.norm_eq_abs,abs_of_nonneg hm.1] at maxStep
  have hv := maxStep.trans ((mul_le_mul_of_nonneg_left hm.2 (by positivity)).trans_eq (mul_one _))
  have h1 := norm_le_norm_sub_add (f m) (f 0)
  intro t ht;exact (show ‖f t‖≤‖f m‖ from hmax ht).trans (by linarith only [h1,hv,norm_nonneg (f 0),kp])

/-- Two solutions, and the transported first variation, on one closed interval. -/
theorem cell_initial_remainder {s : ℝ} (hs : |s|≤1/100) {x y : ℝ→State}
    (dx : FollowsState s x) (dy : FollowsState s y)
    (bx : ∀t∈unitCell,StateBox (x t)) (by0 : ∀t∈unitCell,StateBox (y t))
    (small : ∀t∈unitCell,‖y t-x t‖≤1)
    (J : ℝ→FlowEnd) (dJ : ∀t∈unitCell,HasDerivWithinAt J (actualCoefficient s x t*J t) unitCell t)
    (v : State) :
    (∀t∈unitCell,‖y t-x t‖≤2*‖y 0-x 0‖) ∧
    ∀t∈unitCell,‖y t-x t-J t v‖≤2*(‖y 0-x 0-J 0 v‖+‖y 0-x 0‖^2) := by
  let e:=fun t=>y t-x t
  have ed (t : ℝ) (ht : t∈unitCell) : HasDerivWithinAt e (s • (field (y t)-field (x t))) unitCell t := by
    apply ((dy t ht).sub (dx t ht)).congr_deriv
    ext i; change s*field (y t) i-s*field (x t) i=s*(field (y t) i-field (x t) i); ring
  have eb (t : ℝ) (ht : t∈unitCell) : ‖s • (field (y t)-field (x t))‖≤(2/5)*‖e t‖+0 := by
    rw [norm_smul,Real.norm_eq_abs,add_zero]
    exact (mul_le_mul hs (field_wide_lip (by0 t ht) (bx t ht)) (norm_nonneg _) (by norm_num)).trans_eq (by dsimp [e];ring)
  have E (t : ℝ) (ht : t∈unitCell) : ‖e t‖≤2*‖e 0‖ := by
    simpa only [add_zero] using cell_differential_bound ed eb (by norm_num) t ht
  refine ⟨E,?_⟩
  let w:=fun t=>e t-J t v
  let dw:=fun t=>s • (field (y t)-field (x t))-(actualCoefficient s x t*J t) v
  have wd (t : ℝ) (ht : t∈unitCell) : HasDerivWithinAt w (dw t) unitCell t := by
    simpa only [w,dw,Pi.sub_def,ContinuousLinearMap.map_zero,add_zero,zero_add] using
      (ed t ht).sub ((dJ t ht).clm_apply (hasDerivWithinAt_const t unitCell v))
  have wb (t : ℝ) (ht : t∈unitCell) : ‖dw t‖≤(2/5)*‖w t‖+‖e 0‖^2 := by
    let L:=fderiv ℝ field (x t)
    have ld : ‖L‖≤40 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro u
      exact (field_fderiv_apply (x t) u ▸ linear_ten (bx t ht) u)
    have qa := field_quadratic_ten (bx t ht 0 (by decide)) (small t ht)
    have lo : ‖s • L (w t)‖≤(2/5)*‖w t‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      have l0 := (L.le_opNorm (w t)).trans (mul_le_mul_of_nonneg_right ld (norm_nonneg _))
      exact (mul_le_mul hs l0 (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    have hi : ‖s • (field (y t)-field (x t)-L (e t))‖≤‖e 0‖^2 := by
      rw [norm_smul,Real.norm_eq_abs]
      have ss := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (E t ht)
      have r := mul_le_mul hs qa (norm_nonneg _) (by norm_num)
      change |s| *‖field (y t)-field (x t)-fderiv ℝ field (x t) (e t)‖≤‖e 0‖^2
      dsimp only [e] at ss ⊢
      nlinarith only [r,ss,sq_nonneg ‖y 0-x 0‖]
    have eq : dw t=s • L (w t)+s • (field (y t)-field (x t)-L (e t)) := by
      change s • (field (y t)-field (x t))-s • L (J t v)=_
      simp only [w,map_sub,smul_sub];abel
    rw [eq];exact (norm_add_le ..).trans (add_le_add lo hi)
  exact cell_differential_bound wd wb (sq_nonneg _)
end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.cell_initial_remainder

