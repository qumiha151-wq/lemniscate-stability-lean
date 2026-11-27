import SolitonClassification.LowBendingArclength

noncomputable section
open MeasureTheory Set
namespace ClosedSimilarity.LowBending.BendingSublevel

/-- The sharp fourth-moment bound, cut at a zero of the periodic function.
Both integrals and the optimal coefficient are proved from the fundamental
theorem of calculus and interval Cauchy–Schwarz. -/
theorem fourth_moment_of_zero_endpoints {a b : ℝ} (hab : a≤b)
    {u v : ℝ → ℝ} (du : ∀s, HasDerivAt u (v s) s) (cv : Continuous v)
    (ua : u a=0) (ub : u b=0) :
    3*(∫ s in a..b, u s^4)^2 ≤ (∫ s in a..b, u s^2)^3*(∫ s in a..b, v s^2) := by
  let V := ∫ s in a..b, u s^2
  let H := fun x => (∫ s in a..x, u s^2)-V/2
  have cu : Continuous u := continuous_iff_continuousAt.mpr (fun s => (du s).continuousAt)
  have cg := cu.pow 2
  have dh (s : ℝ) : HasDerivAt H (u s^2) s := by
    exact (intervalIntegral.integral_hasDerivAt_right (cg.intervalIntegrable a s)
      cg.stronglyMeasurable.stronglyMeasurableAtFilter cg.continuousAt).sub_const _
  have ch : Continuous H := continuous_iff_continuousAt.mpr (fun s => (dh s).continuousAt)
  have ha : H a = -V/2 := by simp [H, neg_div]
  have hb : H b = V/2 := by dsimp only [H]; change V - V/2 = V/2; ring
  have dprod (s : ℝ) : HasDerivAt (fun x => H x * (u x)^2)
      (u s^4+2*(H s*u s*v s)) s := by
    apply ((dh s).mul ((du s).pow 2)).congr_deriv
    dsimp
    ring
  have cflux := (ch.mul cu).mul cv
  have cterm := (cu.pow 4).add (cflux.const_mul 2)
  have ex := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b)
    (fun s _ => dprod s) (cterm.intervalIntegrable a b)
  rw [ua,ub] at ex
  have endeq : (∫ s in a..b, u s^4) = -2*(∫ s in a..b, H s*u s*v s) := by
    rw [intervalIntegral.integral_add (f:=fun s => u s^4) (g:=fun s => 2*(H s*u s*v s))
      ((cu.pow 4).intervalIntegrable a b) ((cflux.const_mul 2).intervalIntegrable a b),
      intervalIntegral.integral_const_mul] at ex
    linarith
  have dcube (s : ℝ) : HasDerivAt (fun x => (H x)^3/3) ((H s*u s)^2) s := by
    apply (((dh s).pow 3).div_const 3).congr_deriv
    dsimp
    ring
  have ex3 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b)
    (fun s _ => dcube s) (((ch.mul cu).pow 2).intervalIntegrable a b)
  rw [ha,hb] at ex3
  have cs := interval_integral_mul_sq_le (ch.mul cu) cv hab
  change (∫ s in a..b, H s*u s*v s)^2 ≤
    (∫ s in a..b, (H s*u s)^2)*(∫ s in a..b,v s^2) at cs
  rw [ex3] at cs
  change 3*(∫ s in a..b,u s^4)^2 ≤ V^3*(∫ s in a..b,v s^2)
  rw [endeq]
  linarith only [cs]

/-- A continuous periodic mean-zero function supplies its own cut via Rolle. -/
theorem periodic_fourth_moment {P : ℝ} (hP : 0<P) {u v : ℝ → ℝ}
    (du : ∀s, HasDerivAt u (v s) s) (cv : Continuous v)
    (pu : Function.Periodic u P) (pv : Function.Periodic v P)
    (avg : (∫ s in 0..P, u s)=0) :
    3*(∫ s in 0..P,u s^4)^2 ≤ (∫ s in 0..P,u s^2)^3*(∫ s in 0..P,v s^2) := by
  let G := fun x => ∫ s in 0..x,u s
  have cu := continuous_iff_continuousAt.mpr (fun s => (du s).continuousAt)
  have dg (s : ℝ) : HasDerivAt G (u s) s :=
    intervalIntegral.integral_hasDerivAt_right (cu.intervalIntegrable 0 s)
      cu.stronglyMeasurable.stronglyMeasurableAtFilter cu.continuousAt
  have cG := continuous_iff_continuousAt.mpr (fun s => (dg s).continuousAt)
  have ends : G 0=G P := by simp [G,avg]
  obtain ⟨z,_,hz⟩ := exists_hasDerivAt_eq_zero hP cG.continuousOn ends (fun s _ => dg s)
  have bound := fourth_moment_of_zero_endpoints (show z≤z+P by linarith)
    du cv hz ((pu z).trans hz)
  have shift (f : ℝ → ℝ) (pf : Function.Periodic f P) (n : ℕ) :
      (∫ s in z..z+P, f s^n) = ∫ s in 0..P,f s^n := by
    have pn : Function.Periodic (fun s => f s^n) P := fun s => congrArg (fun x => x^n) (pf s)
    simpa only [zero_add] using pn.intervalIntegral_add_eq z 0
  rwa [shift u pu 4,shift u pu 2,shift v pv 2] at bound

/-- Applied to the actual arclength curvature of a closed immersion. -/
theorem curvature_fourth_moment (c : ClosedFrenetCurve) (μ : ℝ)
    (avg : (∫ s in 0..c.period,c.curvature s-μ)=0) :
    3*(∫ s in 0..c.period,(c.curvature s-μ)^4)^2 ≤
      (∫ s in 0..c.period,(c.curvature s-μ)^2)^3*(∫ s in 0..c.period,c.curvature₁ s^2) :=
  periodic_fourth_moment c.period_pos (fun s => (c.curvature_deriv s).sub_const μ)
    c.curvature₁_continuous (fun s => congrArg (fun x => x-μ) (c.curvature_periodic s))
    c.curvature₁_periodic avg

end ClosedSimilarity.LowBending.BendingSublevel
namespace ClosedSimilarity.LowBending.BendingSublevel

/-- Center the signed curvature moments before estimating the fourth power. -/
theorem necessary_quartic {L μ σ V I₃ I₄ Q : ℝ}
    (hm : 0<μ) (hs : 1≤σ) (variance : V=L*μ^2*(σ^2-1))
    (cubic : 2*(L*μ^3+3*μ*V+I₃)≤(L*μ^2+V)*μ*(1+σ))
    (virial : μ^2*(L*μ^2+V) ≤ -2*Q+L*μ^4+6*μ^2*V+4*μ*I₃+I₄) :
    Q+(5/2-σ-1/(σ+1))*μ^2*V≤I₄/2 := by
  have nz : σ+1 ≠ 0 := by linarith
  have id : μ*((L*μ^2+V)*μ*(1+σ)-2*L*μ^3-6*μ*V) =
      μ^2*V*(σ+1/(σ+1)-5) := by
    rw [variance]; field_simp [nz]; ring
  have upper : 2*μ*I₃ ≤ μ^2*V*(σ+1/(σ+1)-5) := by
    rw [←id]
    linarith only [mul_le_mul_of_nonneg_left cubic hm.le]
  linarith only [virial,upper]

theorem sublevel_constants {d σ μ V : ℝ}
    (hd : d≤36) (hs : 1≤σ) (hm : 0<μ)
    (ratio : 4*Real.pi^2*(σ^2-1)=d) (mass : 2*Real.pi*V=d*μ) :
    69/100 ≤ 5/2-σ-1/(σ+1) ∧ V≤(900/157)*μ := by
  have pi : (157/50:ℝ)<Real.pi := by linarith only [Real.pi_gt_d2]
  have p2 : (157/50:ℝ)^2<Real.pi^2 := by nlinarith only [pi,sq_nonneg (Real.pi-157/50)]
  have ss : 0≤σ^2-1 := by nlinarith only [hs,sq_nonneg (σ-1)]
  have cap : σ≤139/100 := by
    by_contra! bad
    have big : (139/100:ℝ)^2<σ^2 := by nlinarith only [bad,sq_nonneg (σ-139/100)]
    nlinarith only [hd,ratio,big,mul_le_mul_of_nonneg_right p2.le ss]
  constructor
  · have p : 0<σ+1 := by linarith
    have r : 1/(σ+1) ≤ 181/100-σ := by
      apply (div_le_iff₀ p).mpr
      nlinarith only [mul_nonneg (sub_nonneg.mpr cap) (show 0≤139/100+σ-81/100 by linarith)]
    linarith only [r]
  · by_contra! bad
    have vpos : 0<V := by linarith
    nlinarith only [mul_lt_mul_of_pos_right pi vpos,
      mul_le_mul_of_nonneg_right hd hm.le,bad,mass]

/-- A noncircular slice cannot satisfy all the necessary inequalities for a
nonnegative product derivative below the stated threshold. -/
theorem incompatible_nondecreasing_slice {d L μ σ V I₃ I₄ Q : ℝ}
    (hd : d≤36) (hm : 0<μ) (hs : 1≤σ) (hv : 0<V) (hq : 0<Q)
    (ratio : 4*Real.pi^2*(σ^2-1)=d) (mass : 2*Real.pi*V=d*μ)
    (variance : V=L*μ^2*(σ^2-1))
    (cubic : 2*(L*μ^3+3*μ*V+I₃)≤(L*μ^2+V)*μ*(1+σ))
    (virial : μ^2*(L*μ^2+V) ≤ -2*Q+L*μ^4+6*μ^2*V+4*μ*I₃+I₄)
    (interpolation : 3*I₄^2≤V^3*Q) : False := by
  obtain ⟨hc,vcap⟩ := sublevel_constants hd hs hm ratio mass
  have mom := necessary_quartic hm hs variance cubic virial
  have low : 2*(Q+(69/100)*μ^2*V) ≤ I₄ := by
    linarith only [mom,mul_le_mul_of_nonneg_right hc (show 0≤μ^2*V by positivity)]
  have pos : 0≤2*(Q+(69/100)*μ^2*V) := by positivity
  have lowerSquare := sq_le_sq' (by linarith only [low,pos] : -(I₄)≤2*(Q+(69/100)*μ^2*V)) low
  have necessary : 48*(69/100)*μ^2*(V*Q) ≤ V^2*(V*Q) := by
    nlinarith only [interpolation,lowerSquare,sq_nonneg (Q-(69/100)*μ^2*V)]
  have gap := le_of_mul_le_mul_right necessary (mul_pos hv hq)
  have v2 := sq_le_sq' (by linarith : -((900/157)*μ)≤V) vcap
  nlinarith only [gap,v2,sq_pos_of_pos hm]

end ClosedSimilarity.LowBending.BendingSublevel
namespace ClosedSimilarity.LowBending.BendingSublevel

/-- Exact centered second, third, and fourth moments of a continuous real
function on the period, retaining the full signed third moment. -/
theorem centered_moments {P μ : ℝ} {k : ℝ → ℝ} (ck : Continuous k)
    (mean : (∫ s in 0..P,k s)=P*μ) :
    let u := fun s => k s-μ
    let V := ∫ s in 0..P,u s^2
    let I₃ := ∫ s in 0..P,u s^3
    (∫ s in 0..P,u s)=0 ∧
    (∫ s in 0..P,k s^2)=P*μ^2+V ∧
    (∫ s in 0..P,k s^3)=P*μ^3+3*μ*V+I₃ ∧
    (∫ s in 0..P,k s^4)=P*μ^4+6*μ^2*V+4*μ*I₃+(∫ s in 0..P,u s^4) := by
  let u := fun s => k s-μ
  have cu : Continuous u := ck.sub continuous_const
  have avg : (∫ s in 0..P,u s)=0 := by
    dsimp only [u]
    rw [intervalIntegral.integral_sub (ck.intervalIntegrable 0 P)
      (continuous_const.intervalIntegrable 0 P),intervalIntegral.integral_const,mean]
    simp
  have h2 (s : ℝ) : k s^2=μ^2+2*μ*u s+u s^2 := by dsimp [u]; ring
  have h3 (s : ℝ) : k s^3=μ^3+(3*μ^2)*u s+(3*μ)*u s^2+u s^3 := by dsimp [u]; ring
  have h4 (s : ℝ) : k s^4=μ^4+(4*μ^3)*u s+(6*μ^2)*u s^2+(4*μ)*u s^3+u s^4 := by dsimp [u]; ring
  refine ⟨avg,?_,?_,?_⟩
  · change (∫ s in 0..P,k s^2) = P*μ^2+∫ s in 0..P,u s^2
    simp_rw [h2]
    simp (disch := exact Continuous.intervalIntegrable (by fun_prop) ..)
      [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,avg]
  · change (∫ s in 0..P,k s^3) = P*μ^3+3*μ*(∫ s in 0..P,u s^2)+∫ s in 0..P,u s^3
    simp_rw [h3]
    simp (disch := exact Continuous.intervalIntegrable (by fun_prop) ..)
      [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,avg]
  · change (∫ s in 0..P,k s^4) = P*μ^4+6*μ^2*(∫ s in 0..P,u s^2)+
      4*μ*(∫ s in 0..P,u s^3)+∫ s in 0..P,u s^4
    simp_rw [h4]
    simp (disch := exact Continuous.intervalIntegrable (by fun_prop) ..)
      [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,avg]

/-- The derivative variance is positive when a genuine, centered curvature
has nonzero variance. The constant-test and fourth-moment bounds avoid any
nondegeneracy hypothesis on the locations of its extrema. -/
theorem positive_gradient_of_variance (c : ClosedFrenetCurve) (μ : ℝ)
    (avg : (∫ s in 0..c.period,c.curvature s-μ)=0)
    (var : 0 < ∫ s in 0..c.period,(c.curvature s-μ)^2) : 0<c.curvatureGradientSquare := by
  let u := fun s => c.curvature s-μ
  have cu : Continuous u := c.curvature_continuous.sub continuous_const
  have bound := curvature_fourth_moment c μ avg
  have cs := interval_integral_mul_sq_le (f:=fun _ : ℝ => (1:ℝ))
    continuous_const (cu.pow 2) c.period_pos.le
  have cs' : (∫ s in 0..c.period,u s^2)^2 ≤ c.period*(∫ s in 0..c.period,u s^4) := by
    simpa [one_mul,←pow_mul] using cs
  have i4 : 0 < ∫ s in 0..c.period,u s^4 := by
    exact pos_of_mul_pos_right ((sq_pos_of_pos var).trans_le cs') c.period_pos.le
  change 3*(∫ s in 0..c.period,u s^4)^2 ≤
    (∫ s in 0..c.period,u s^2)^3*c.curvatureGradientSquare at bound
  exact pos_of_mul_pos_right ((show 0<3*(∫ s in 0..c.period,u s^4)^2 by positivity).trans_le bound)
    (pow_nonneg var.le _)

end ClosedSimilarity.LowBending.BendingSublevel
namespace ClosedSimilarity.LowBending.BendingSublevel

/-- A unit spinor whose square has zero mean has centered second moment
at least half the period. All averages use the actual interval measure. -/
theorem spinor_variance {L : ℝ} (hL : 0<L) {S : ℝ → ℂ} (cs : Continuous S)
    (unit : ∀s, ‖S s‖=1) (square : (∫ s in 0..L,S s^2)=0) :
    let m := (∫ s in 0..L,S s)/(L:ℂ)
    L≤2*(∫ s in 0..L, ‖S s-m‖^2) := by
  let m := (∫ s in 0..L,S s)/(L:ℂ)
  let h := fun s => S s-m
  have ch : Continuous h := cs.sub continuous_const
  have lm : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  have avg : (∫ s in 0..L,h s)=0 := by
    dsimp only [h]
    rw [intervalIntegral.integral_sub (cs.intervalIntegrable 0 L)
      (continuous_const.intervalIntegrable 0 L),intervalIntegral.integral_const]
    simp only [sub_zero,Complex.real_smul,m]
    field_simp
    ring
  have ih : (∫ s in 0..L,inner ℝ m (h s))=0 := by
    change (∫ s in 0..L,(innerSL ℝ m) (h s))=0
    rw [ContinuousLinearMap.intervalIntegral_comp_comm _ (ch.intervalIntegrable ..),avg,map_zero]
  have sum (s : ℝ) : m+h s=S s := by dsimp [h]; ring
  have npoint (s : ℝ) : (1:ℝ)=‖m‖^2+2*inner ℝ m (h s)+‖h s‖^2 := by
    rw [←norm_add_sq_real,sum,unit]; norm_num
  have nint := congrArg (fun f : ℝ → ℝ => ∫ s in 0..L, f s) (funext npoint)
  change (∫ _ in 0..L,(1:ℝ))=∫ s in 0..L,‖m‖^2+2*inner ℝ m (h s)+‖h s‖^2 at nint
  have ci : Continuous (fun s => inner ℝ m (h s)) := continuous_const.inner ch
  rw [intervalIntegral.integral_add (f:=fun s => ‖m‖^2+2*inner ℝ m (h s))
    (g:=fun s => ‖h s‖^2) ((continuous_const.add (ci.const_mul 2)).intervalIntegrable ..)
    ((ch.norm.pow 2).intervalIntegrable ..),intervalIntegral.integral_add
    (f:=fun _ : ℝ => ‖m‖^2) (g:=fun s => 2*inner ℝ m (h s)) (continuous_const.intervalIntegrable ..)
    ((ci.const_mul 2).intervalIntegrable ..),intervalIntegral.integral_const_mul,ih] at nint
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one,mul_zero,add_zero] at nint
  have ppoint (s : ℝ) : S s^2=m^2+(2*m)*h s+(h s)^2 := by rw [←sum s]; ring
  have pint := congrArg (fun f : ℝ → ℂ => ∫ s in 0..L,f s) (funext ppoint)
  change (∫ s in 0..L,S s^2)=∫ s in 0..L,m^2+(2*m)*h s+(h s)^2 at pint
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) ..)
    [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,avg,square,Complex.real_smul] at pint
  have eq : (∫ s in 0..L,(h s)^2)= -((L:ℂ)*m^2) := by linear_combination -pint
  have triangle := intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (f:=fun s => (h s)^2) hL.le
  rw [eq,norm_neg,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL] at triangle
  simp only [norm_pow] at triangle
  change L≤2*(∫ s in 0..L,‖h s‖^2)
  linarith only [nint,triangle]

end ClosedSimilarity.LowBending.BendingSublevel
