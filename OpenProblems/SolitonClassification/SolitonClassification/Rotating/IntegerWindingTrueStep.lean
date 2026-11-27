import SolitonClassification.Rotating.IntegerWindingLocalMajorant

namespace SolitonClassification.Rotating.IntegerWinding
noncomputable section
open Set Metric Polynomial UniversalMajorant ODE
open scoped NNReal Topology
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

private def wholeBox : Set State := {a | |a 0| ≤ 9 ∧ |a 1| ≤ 5 ∧
    |a 2| ≤ 8 ∧ |a 3| ≤ 8 ∧ |a 4| ≤ 1}

private theorem ball_subset {a : State} (ha : a ∈ nodeBox) :
    closedBall a (3/5) ⊆ wholeBox := by
  intro x hx
  have hnorm : ‖x-a‖ ≤ 3/5 := mem_closedBall_iff_norm.mp hx
  have h (i : Fin 6) : |x i| ≤ 3/5+|a i| := by
    have hcoord := (coordinate_bound (x-a) i).trans hnorm
    calc
      _ = |(x i-a i)+a i| := by rw [sub_add_cancel]
      _ ≤ |x i-a i|+|a i| := abs_add_le _ _
      _ ≤ _ := add_le_add hcoord le_rfl
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  exact ⟨by linarith [h 0],by linarith [h 1],by linarith [h 2],
    by linarith [h 3],by linarith [h 4]⟩

private theorem whole_field {a : State} (ha : a ∈ wholeBox) : ‖field a‖ ≤ 75 := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  fin_cases i
  · change |8*a 1| ≤ 75
    rw [abs_mul]; norm_num; linarith
  · change |-(a 0)^3/16-a 2/8-a 4*a 3/8| ≤ 75
    calc
      _ ≤ |-(a 0)^3/16-a 2/8|+|a 4*a 3/8| := abs_sub _ _
      _ ≤ (|-(a 0)^3/16|+|a 2/8|)+|a 4*a 3/8| := by gcongr; apply abs_sub
      _ = |a 0|^3/16+|a 2|/8+|a 4| * |a 3|/8 := by simp [abs_div,abs_mul,abs_pow]
      _ ≤ (9)^3/16+(8)/8+1*(8)/8 := by gcongr
      _ ≤ 75 := by norm_num
  · change |-a 0*a 3| ≤ 75
    rw [abs_mul,abs_neg]
    calc
      _ ≤ (9:ℝ)*(8) := by gcongr
      _ ≤ 75 := by norm_num
  · change |1+a 0*a 2| ≤ 75
    calc
      _ ≤ |(1:ℝ)|+|a 0*a 2| := abs_add_le _ _
      _ = 1+|a 0| * |a 2| := by simp [abs_mul]
      _ ≤ 1+(9)*(8) := by gcongr
      _ ≤ 75 := by norm_num
  · simp [field]
  · change |a 0| ≤ 75
    linarith

private theorem whole_linear {a : State} (ha : a∈wholeBox) (u : State) :
    ‖linear a u‖≤18*‖u‖ := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
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
      _ ≤ 3*(9)^2*‖u‖/16+‖u‖/8+1*‖u‖/8+‖u‖*(8)/8 := by
        gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith
  · change |-a 0*u 3-u 0*a 3|≤_
    calc
      _ ≤ |-a 0*u 3|+|u 0*a 3| := abs_sub _ _
      _ = |a 0| * |u 3|+|u 0| * |a 3| := by simp [abs_mul]
      _ ≤ (9)*‖u‖+‖u‖*(8) := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith
  · change |a 0*u 2+u 0*a 2|≤_
    calc
      _ ≤ |a 0*u 2|+|u 0*a 2| := abs_add_le _ _
      _ = |a 0| * |u 2|+|u 0| * |a 2| := by simp [abs_mul]
      _ ≤ (9)*‖u‖+‖u‖*(8) := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith
  · simp [linear]
  · change |u 0|≤_
    linarith [coordinate_bound u 0]

private theorem ball_lipschitz {a : State} (ha : a ∈ nodeBox) :
    LipschitzOnWith 18 field (closedBall a (3/5)) := by
  apply (convex_closedBall a (3/5)).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜:=ℝ)
  · intro x _
    exact field_smooth.differentiable (by simp) x
  · intro x hx
    apply (fderiv ℝ field x).opNorm_le_bound (by norm_num)
    intro v
    rw [field_fderiv_apply]
    exact whole_linear (ball_subset ha hx) v

private theorem short_solution {a : State} (ha : a ∈ nodeBox) (σ : ℝ) (hσ : |σ|≤1) :
    ∃ x : ℝ → State, x 0=a ∧
      (∀t ∈ Ioo (-(1/125:ℝ)) (1/125), HasDerivAt x (σ • field (x t)) t) ∧
      (∀t, x t ∈ closedBall a (3/5)) := by
  let t₀ : Icc (-(1/125:ℝ)) (1/125) := ⟨0, by norm_num⟩
  let v := fun (_ : ℝ) (y : State) => σ • field y
  have hp : IsPicardLindelof v t₀ a (3/5) 0 75 18 := by
    constructor
    · intro t _
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro x hx y hy
      change ‖σ • field x-σ • field y‖ ≤ 18*‖x-y‖
      rw [←smul_sub]
      exact (norm_smul_le_of_abs_le_one σ hσ _).trans
        (lipschitzOnWith_iff_norm_sub_le.mp (ball_lipschitz ha) hx hy)
    · intro _ _
      exact continuousOn_const
    · intro t ht x hx
      exact (norm_smul_le_of_abs_le_one σ hσ _).trans (whole_field (ball_subset ha hx))
    · norm_num [t₀]
  have hx : a ∈ closedBall a (0:ℝ≥0) := mem_closedBall_self le_rfl
  obtain ⟨z,hz⟩ := FunSpace.exists_isFixedPt_next hp hx
  refine ⟨z.compProj, ?_, ?_, fun _ => z.compProj_mem_closedBall hp.mul_max_le⟩
  · change z.compProj (t₀:ℝ)=a
    rw [FunSpace.compProj_val,←hz,FunSpace.next_apply₀]
  · intro t ht
    have hI : t ∈ Icc (-(1/125:ℝ)) (1/125) := Ioo_subset_Icc_self ht
    apply HasDerivWithinAt.hasDerivAt (s:=Icc (-(1/125:ℝ)) (1/125)) _ (Icc_mem_nhds ht.1 ht.2)
    apply hasDerivWithinAt_picard_Icc t₀.2 hp.continuousOn_uncurry
      z.continuous_compProj.continuousOn (fun _ _ => z.compProj_mem_closedBall hp.mul_max_le)
      a hI |>.congr_of_mem _ hI
    intro t' ht'
    nth_rw 1 [←hz]
    rw [FunSpace.compProj_of_mem ht',FunSpace.next_apply]

private theorem small_gronwall {t ε : ℝ} (hε : 0≤ε) (ht : 0≤t) (hT : t≤1/125) :
    gronwallBound 0 18 ε t≤2*ε*t := by
  have hpos : 0≤18*t := by positivity
  have hex := Real.abs_exp_sub_one_le (show |18*t|≤1 by rw [abs_of_nonneg hpos]; linarith)
  rw [abs_of_nonneg hpos] at hex
  have he : Real.exp (18*t)-1≤2*(18*t) := (le_abs_self _).trans hex
  simp only [gronwallBound,show (18:ℝ)≠0 by norm_num,if_false,zero_mul,zero_add]
  nlinarith [mul_le_mul_of_nonneg_left he hε]

/-- Each enlarged-box input has a trajectory of the original polynomial field,
whose true endpoint is enclosed by the same degree-60 polynomial for either time sign.
The bound holds throughout the entire indicated interval. -/
theorem exists_true_taylor_step {a : State} (ha : a ∈ nodeBox) (σ : ℝ) (hσ : |σ|≤1) :
    ∃ x : ℝ → State, x 0=a ∧
      (∀t ∈ Ioo (-(1/125:ℝ)) (1/125), HasDerivAt x (σ • field (x t)) t) ∧
      ∀t ∈ Icc 0 (universalStepCap:ℝ),
        ‖x t-polynomialPath (taylorPolynomial a 60) (σ*t)‖ ≤ (2:ℝ)/10^59 := by
  obtain ⟨x,h0,hx,hball⟩ := short_solution ha σ hσ
  refine ⟨x,h0,hx,?_⟩
  let p := fun t => polynomialPath (taylorPolynomial a 60) (σ*t)
  let v := fun t => polynomialVelocity (taylorPolynomial a 60) (σ*t)
  let ε : ℝ := 1/10^57
  have hcap : (universalStepCap:ℝ)<1/125 := by norm_num [universalStepCap]
  have htime {s : ℝ} (hs : s∈Icc 0 (universalStepCap:ℝ)) :
      s∈Ioo (-(1/125:ℝ)) (1/125) := ⟨by linarith [hs.1],hs.2.trans_lt hcap⟩
  have hscaled {s : ℝ} (hs : s∈Icc 0 (universalStepCap:ℝ)) :
      |σ*s| ≤ (universalStepCap:ℝ) := by
    rw [abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_right hσ hs.1).trans (by simpa using hs.2)
  have hP (s : ℝ) : HasDerivAt p (σ • v s) s := signedPolynomial_hasDerivAt σ _ s
  have hc : ContinuousOn (fun t => x t-p t) (Icc 0 (universalStepCap:ℝ)) :=
    fun s hs => ((hx s (htime hs)).sub (hP s)).continuousAt.continuousWithinAt
  have hd s (hs : s ∈ Ico 0 (universalStepCap:ℝ)) :
      HasDerivWithinAt (fun t=>x t-p t) (σ • field (x s)-σ • v s) (Ici s) s :=
    ((hx s (htime (Ico_subset_Icc_self hs))).sub (hP s)).hasDerivWithinAt
  have hinit : ‖x 0-p 0‖≤0 := by simp [p,h0,polynomialPath_taylor_zero]
  have hb s (hs : s∈Ico 0 (universalStepCap:ℝ)) :
      ‖σ • field (x s)-σ • v s‖ ≤ 18*‖x s-p s‖+ε := by
    have hs' := hscaled (Ico_subset_Icc_self hs)
    have hp : p s ∈ closedBall a (3/5) :=
      mem_closedBall_iff_norm.mpr ((node_excursion ha hs').trans (by norm_num))
    have hl : ‖field (x s)-field (p s)‖ ≤ 18*‖x s-p s‖ :=
      lipschitzOnWith_iff_norm_sub_le.mp (ball_lipschitz ha) (hball s) hp
    have hr : ‖v s-field (p s)‖ ≤ ε := by
      change ‖polynomialVelocity _ _-field (polynomialPath _ _)‖≤_
      rw [←polynomial_residual_actual]
      exact node_residual ha hs'
    rw [←smul_sub]
    apply (norm_smul_le_of_abs_le_one σ hσ _).trans
    calc
      _ ≤ ‖field (x s)-field (p s)‖+‖field (p s)-v s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add hl (by rwa [norm_sub_rev])
  have he := norm_le_gronwallBound_of_norm_deriv_right_le hc hd hinit hb
  intro t ht
  have he' := he t ht
  simp only [sub_zero] at he'
  refine he'.trans ((small_gronwall (by positivity : 0≤ε) ht.1 (ht.2.trans hcap.le)).trans ?_)
  exact (mul_le_mul_of_nonneg_left ht.2 (by positivity : 0≤2*ε)).trans (by norm_num [ε,universalStepCap])

end
end SolitonClassification.Rotating.IntegerWinding

#print axioms SolitonClassification.Rotating.IntegerWinding.exists_true_taylor_step
