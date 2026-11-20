import SolitonClassification.FrozenEscapeAmplitude

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.FrozenStress.Orbit
variable (z : Orbit)

private theorem bounded_components_of_barrier {M : ℝ} (mp : 0≤M) (zero : z.radial 0=0)
    (bar : ∀t≥0,-z.radial t≤M) : ∃K>0,∀t≥0, |z.k t|≤K ∧ |z.v t|≤K := by
  let B := 12+4*(M+4)
  let V := M+B+1
  have bp : 0<B := by dsimp [B]; linarith
  have vp : 0<V := by dsimp [V]; linarith
  refine ⟨V+1,by linarith,?_⟩
  intro t ht
  have rh : z.radial t≤0 := (z.radial_antitone ht).trans_eq zero
  have ra : |z.radial t|≤M := by rw [abs_of_nonpos rh]; exact bar t ht
  have tr : |z.transverse t|≤B := z.transverse_bound_of_radial_barrier mp zero bar t ht
  have r2 := pow_le_pow_left₀ (abs_nonneg _) ra 2
  have tr2 := pow_le_pow_left₀ (abs_nonneg _) tr 2
  rw [sq_abs] at r2 tr2
  have vs : z.amplitude t^2≤V^2 := by
    dsimp [V]; nlinarith only [z.stress_unit t,r2,tr2,mul_nonneg mp bp.le,mp,bp]
  have vv : |z.v t|≤V := abs_le_of_sq_le_sq (by nlinarith only [z.amplitude_sq t,vs,sq_nonneg (z.k t^2/2)]) vp.le
  have kv : z.k t^2/2≤V := le_of_sq_le_sq (by nlinarith only [vs,z.amplitude_sq t,sq_nonneg (z.v t)]) vp.le
  refine ⟨?_,by linarith⟩
  exact abs_le_of_sq_le_sq (by nlinarith only [kv,sq_nonneg V]) (by positivity)

private theorem radial_zero_limit_of_barrier {M : ℝ} (mp : 0≤M) (zero : z.radial 0=0)
    (bar : ∀t≥0,-z.radial t≤M) : Tendsto z.radial atTop (𝓝 0) := by
  obtain ⟨K,kp,bk⟩ := z.bounded_components_of_barrier mp zero bar
  have bl : BddBelow (range z.radial) := by
    refine ⟨-M,?_⟩
    rintro y ⟨x,rfl⟩
    rcases le_total 0 x with h|h
    · linarith only [bar x h]
    · linarith only [z.radial_antitone h,zero,mp]
  have rl := tendsto_atTop_ciInf z.radial_antitone bl
  have gp (t : ℝ) : HasDerivAt (fun s => -(z.p s)^2) (2*z.p t*z.k t*z.q t) t := by
    convert! ((z.dp t).pow 2).neg using 1
    ring
  have gb (t : ℝ) (ht : 0≤t) : |2*z.p t*z.k t*z.q t|≤2*K := by
    simp only [abs_mul,show |(2:ℝ)|=2 by norm_num]
    have a := z.angle_bounds t
    have k := (bk t ht).1
    calc
      _ ≤ 2*1*K*1 := by gcongr <;> first | exact a.1 | exact a.2
      _ = _ := by ring
  have p2 := derivative_vanishes_on_tail z.radial_hasDerivAt gp gb rl
  have p2pos : Tendsto (fun t => (z.p t)^2) atTop (𝓝 0) := by simpa only [neg_neg,neg_zero] using p2.neg
  have plim : Tendsto z.p atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp p2pos
  have dj (t : ℝ) : HasDerivAt (fun s => -z.k s*z.q s)
      (-(z.v t*z.q t)-z.k t^2*z.p t) t := by
    convert! (z.dk t).neg.mul (z.dq t) using 1
    simp only [Pi.neg_apply]; ring
  have jb (t : ℝ) (ht : 0≤t) : |-(z.v t*z.q t)-z.k t^2*z.p t|≤K+K^2 := by
    apply (abs_sub ..).trans
    simp only [abs_neg,abs_mul,abs_pow]
    obtain ⟨k,v⟩:=bk t ht
    obtain ⟨p,q⟩:=z.angle_bounds t
    calc
      _ ≤ K*1+K^2*1 := by gcongr
      _ = _ := by ring
  have jl := derivative_vanishes_on_tail z.dp dj jb plim
  have htail : ∀ᶠ t : ℝ in atTop, ‖z.radial t‖≤K/2*|-z.k t*z.q t|+K*|z.p t| := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    obtain ⟨k,v⟩ := bk t ht
    rw [Real.norm_eq_abs,Orbit.radial]
    apply (abs_add_le ..).trans
    rw [show z.k t^2/2*z.q t=(z.k t/2)*(z.k t*z.q t) by ring]
    simp only [abs_mul,abs_neg,abs_div,show |(2:ℝ)|=2 by norm_num]
    exact add_le_add (mul_le_mul_of_nonneg_right (by linarith : |z.k t|/2≤K/2) (by positivity))
      (mul_le_mul_of_nonneg_right v (abs_nonneg _))
  apply squeeze_zero_norm' htail
  simpa only [abs_zero,mul_zero,add_zero] using (jl.abs.const_mul (K/2)).add (plim.abs.const_mul K)

/-- Every real global solution of the frozen polynomial ODE through a symmetric seam
reaches arbitrarily high outgoing radial stress, with no restriction on its seam curvature. -/
theorem outgoing_radial_tendsto_atTop (zero : z.radial 0=0) (p0 : z.p 0=1) :
    Tendsto (fun t => -z.radial t) atTop atTop := by
  have hm : Monotone (fun t => -z.radial t) := fun _ _ h => neg_le_neg (z.radial_antitone h)
  apply tendsto_atTop.2
  intro R
  by_contra! bad
  have upper (t : ℝ) : -z.radial t≤R := by
    by_contra! above
    exact bad ((eventually_ge_atTop t).mono (fun x hx => not_lt_of_ge (above.le.trans (hm hx))))
  have mp : 0≤R := by simpa only [zero,neg_zero] using upper 0
  have lim := z.radial_zero_limit_of_barrier mp zero (fun t _ => upper t)
  have flat (t : ℝ) (ht : 0≤t) : z.radial t=0 := by
    have zle := (z.radial_antitone ht).trans_eq zero
    have ge : 0≤z.radial t := le_of_tendsto lim ((eventually_ge_atTop t).mono (fun x hx => z.radial_antitone hx))
    exact le_antisymm zle ge
  have d : HasDerivWithinAt z.radial 0 (Ici 0) 0 :=
    (hasDerivWithinAt_const 0 (Ici 0) (0:ℝ)).congr (fun x hx => flat x hx) zero
  have uq : UniqueDiffWithinAt ℝ (Ici (0:ℝ)) 0 := uniqueDiffOn_Ici 0 0 (mem_Ici.mpr le_rfl)
  have eq := ((z.radial_hasDerivAt 0).hasDerivWithinAt.derivWithin uq).symm.trans (d.derivWithin uq)
  rw [p0] at eq
  norm_num at eq

theorem seam_reaches_all_radial_levels {c : ℝ} (_k0 : z.k 0=c) (v0 : z.v 0=0)
    (p0 : z.p 0=1) (q0 : z.q 0=0) {R : ℝ} (rp : 0≤R) :
    ∃t≥0, -z.radial t=R := by
  have zero : z.radial 0=0 := by simp [Orbit.radial,v0,q0]
  obtain ⟨t,ht,large⟩ := ((eventually_ge_atTop (0:ℝ)).and
    ((z.outgoing_radial_tendsto_atTop zero p0).eventually_ge_atTop R)).exists
  have ct : Continuous (fun t => -z.radial t) := (continuous_iff_continuousAt.mpr
    (fun t => (z.radial_hasDerivAt t).continuousAt)).neg
  obtain ⟨x,hx,hit⟩ := intermediate_value_Icc ht ct.continuousOn (show R∈Icc (-z.radial 0) (-z.radial t) from
    ⟨by simpa only [zero,neg_zero] using rp,large⟩)
  exact ⟨x,hx.1,hit⟩

/-- On one final half-line every sufficiently high corrected section is crossed
exactly once and with a uniformly positive derivative in the outgoing clock. -/
theorem seam_corrected_sections (zero : z.radial 0=0) (p0 : z.p 0=1) :
    ∃S≥0, (∀x≥S,12≤z.amplitude x ∧ 1/4≤deriv z.outgoingHeight x) ∧
      Tendsto z.outgoingHeight atTop atTop ∧
      ∀R≥z.outgoingHeight S,∃! x : ℝ, S≤x ∧ z.outgoingHeight x=R := by
  have escape := z.outgoing_radial_tendsto_atTop zero p0
  obtain ⟨S,hS,high⟩ := ((eventually_ge_atTop (0:ℝ)).and (escape.eventually_ge_atTop 12)).exists
  have highA (x : ℝ) (hx : S≤x) : 12≤z.amplitude x := by
    have rs := z.radial_antitone hx
    have nn : 0≤z.amplitude x := Real.sqrt_nonneg _
    have ha : -z.radial x≤z.amplitude x := by nlinarith [z.stress_unit x,sq_nonneg (z.transverse x)]
    linarith
  have hd (x : ℝ) (hx : S≤x) : DifferentiableAt ℝ z.outgoingHeight x :=
    (z.corrected_outgoing_rate x (by linarith [highA x hx])).differentiableAt
  have grow : Tendsto z.outgoingHeight atTop atTop := by
    apply tendsto_atTop.2
    intro R
    filter_upwards [eventually_ge_atTop S,escape.eventually_ge_atTop (R+1)] with x hx hr
    have r := (abs_le.mp (z.large_amplitude_height (highA x hx)).1).1
    linarith
  have sm : StrictMonoOn z.outgoingHeight (Ici S) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    rw [interior_Ici]
    intro x hx
    exact lt_of_lt_of_le (by norm_num) (z.large_amplitude_height (highA x (mem_Ioi.mp hx).le)).2
  refine ⟨S,hS,fun x hx => ⟨highA x hx,(z.large_amplitude_height (highA x hx)).2⟩,grow,?_⟩
  intro R hR
  obtain ⟨T,hT,hr⟩ := ((eventually_ge_atTop S).and (grow.eventually_ge_atTop R)).exists
  have cc : ContinuousOn z.outgoingHeight (Icc S T) := fun x hx => (hd x hx.1).continuousAt.continuousWithinAt
  obtain ⟨x,hx,eq⟩ := intermediate_value_Icc hT cc (show R∈Icc (z.outgoingHeight S) (z.outgoingHeight T)
    from ⟨hR,hr⟩)
  exact ⟨x,⟨hx.1,eq⟩,fun y hy => sm.injOn hy.1 hx.1 (hy.2.trans eq.symm)⟩

end ClosedSimilarity.FrozenStress.Orbit
#print axioms ClosedSimilarity.FrozenStress.Orbit.seam_reaches_all_radial_levels
#print axioms ClosedSimilarity.FrozenStress.Orbit.seam_corrected_sections
