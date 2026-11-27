import Migration.AngularReconstruction

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.AngularExcursion

def weight (q z : ℝ) := Real.sqrt (Real.cos z+q)
def cost (q lo hi : ℝ) := 2*(∫ z in lo..hi, weight q z)^2

private theorem doubled {g b : ℝ→ℝ} {P x y : ℝ} (hp : g P=g 0)
    (dg : ∀s,HasDerivAt g (b s) s) (cb : Continuous b)
    (hx : x∈Icc 0 P) (hy : y∈Icc 0 P) :
    2*|g y-g x|≤∫s in (0:ℝ)..P,|b s| := by
  have seg (r t : ℝ) (rt : r≤t) : |g t-g r|≤∫s in r..t,|b s| := by
    rw [←intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>dg s) (cb.intervalIntegrable ..)]
    exact intervalIntegral.abs_integral_le_integral_abs rt
  have ordered (r t : ℝ) (hr : 0≤r) (hrt : r≤t) (ht : t≤P) :
      2*|g t-g r|≤∫s in (0:ℝ)..P,|b s| := by
    have a := seg 0 r hr
    have b' := seg r t hrt
    have c := seg t P ht
    rw [hp] at c
    have l := abs_sub_le (g t) (g 0) (g r)
    rw [abs_sub_comm (g t) (g 0),abs_sub_comm (g 0) (g r)] at l
    have j := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (cb.abs.intervalIntegrable 0 r) (cb.abs.intervalIntegrable r t)
    have k := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (cb.abs.intervalIntegrable 0 t) (cb.abs.intervalIntegrable t P)
    linarith only [a,b',c,l,j,k]
  rcases le_total x y with h|h
  · exact ordered x y hx.1 h hy.2
  · rw [abs_sub_comm]; exact ordered y x hy.1 h hx.2

/-- In arclength coordinates D is an upper bound for the projected period
displacement. The multiplier q allows excursions extending past a semicircle.
An exactly closed slice permits D=0 for every direction. -/
theorem weighted_excursion {P D q lo hi : ℝ} {θ k : ℝ→ℝ}
    (p : 0≤P) (dθ : ∀s, HasDerivAt θ (k s) s) (ck : Continuous k)
    (endθ : θ P=θ 0) (lohit : ∃x∈Icc 0 P,θ x=lo) (hihit : ∃x∈Icc 0 P,θ x=hi)
    (valid : ∀s∈Icc 0 P,0≤Real.cos (θ s)+q)
    (displacement : (∫s in (0:ℝ)..P,Real.cos (θ s))≤D) :
    cost q lo hi ≤ ((∫s in (0:ℝ)..P,(k s)^2)/2)*(D+P*q) := by
  have cθ := continuous_iff_continuousAt.mpr fun s => (dθ s).continuousAt
  have cw : Continuous (weight q) := (Real.continuous_cos.add continuous_const).sqrt
  let H := fun y => ∫z in lo..y,weight q z
  have dh (s : ℝ) : HasDerivAt H (weight q s) s :=
    intervalIntegral.integral_hasDerivAt_right (cw.intervalIntegrable ..)
      (cw.stronglyMeasurableAtFilter _ _) cw.continuousAt
  let b := fun s=>weight q (θ s)*k s
  have cb : Continuous b := (cw.comp cθ).mul ck
  obtain ⟨x,hx,ex⟩ := lohit
  obtain ⟨y,hy,ey⟩ := hihit
  have variation := doubled (g:=H ∘ θ) (b:=b) (by simp only [Function.comp_apply,endθ])
    (fun s => (dh _).comp s (dθ s)) cb hx hy
  simp only [Function.comp_apply,ex,ey,H,intervalIntegral.integral_same,sub_zero] at variation
  have ident (s : ℝ) : |b s|=|k s| * weight q (θ s) := by
    dsimp [b,weight]; rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]; ring
  simp_rw [ident] at variation
  have cs := Flow.interval_integral_mul_sq_le ck.abs (cw.comp cθ) p
  simp only [sq_abs,Function.comp_apply] at cs
  have integr : (∫s in (0:ℝ)..P,(weight q (θ s))^2)=
      (∫s in (0:ℝ)..P,Real.cos (θ s))+P*q := by
    unfold weight
    rw [intervalIntegral.integral_congr (g:=fun s => Real.cos (θ s)+q)
      (fun s hs => Real.sq_sqrt (valid s (by rwa [uIcc_of_le p] at hs))),
      intervalIntegral.integral_add (f:=fun s=>Real.cos (θ s)) (g:=fun _=>q) ((Real.continuous_cos.comp cθ).intervalIntegrable ..)
        intervalIntegrable_const,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  rw [integr] at cs
  have b2 := pow_le_pow_left₀ (show 0≤2*|∫z in lo..hi,weight q z| by positivity) variation 2
  rw [mul_pow,sq_abs] at b2
  have kn : 0≤∫s in (0:ℝ)..P,(k s)^2 := intervalIntegral.integral_nonneg p (fun s _=> sq_nonneg _)
  have cor := mul_le_mul_of_nonneg_left (add_le_add_right displacement (P*q)) kn
  dsimp only [cost]; linarith only [b2,cs,cor]

theorem semicircle {P d : ℝ} {θ k : ℝ→ℝ}
    (p : 0≤P) (dθ : ∀s,HasDerivAt θ (k s) s) (ck : Continuous k)
    (endθ : θ P=θ 0) (lo : ∃x∈Icc 0 P,θ x= -(Real.pi/2))
    (hi : ∃x∈Icc 0 P,θ x=Real.pi/2)
    (inside : ∀s∈Icc 0 P,θ s∈Icc (-(Real.pi/2)) (Real.pi/2))
    (disp : (∫s in (0:ℝ)..P,Real.cos (θ s))≤d) :
    cost 0 (-(Real.pi/2)) (Real.pi/2) ≤ ((∫s in (0:ℝ)..P,(k s)^2)/2)*d := by
  have valid (s : ℝ) (hs : s∈Icc 0 P) : 0≤Real.cos (θ s)+0 := by
    simpa only [add_zero] using Real.cos_nonneg_of_mem_Icc (inside s hs)
  simpa only [mul_zero,add_zero] using weighted_excursion (q:=0) p dθ ck endθ lo hi valid disp

def directionalWeight (z : ℝ) := Real.sqrt |Real.cos z|
def halfPeriodMass := ∫z in (0:ℝ)..Real.pi,directionalWeight z

private theorem range_from_closure {P : ℝ} {θ : ℝ → ℝ} (pp : 0<P) (cθ : Continuous θ)
    (hx : (∫s in (0:ℝ)..P,Real.cos (θ s))=0)
    (hy : (∫s in (0:ℝ)..P,Real.sin (θ s))=0) :
    ∃ x∈Icc 0 P,∃ y∈Icc 0 P,θ x+Real.pi≤θ y := by
  obtain ⟨x,ax,l⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr pp.le) cθ.continuousOn
  obtain ⟨y,ay,h⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr pp.le) cθ.continuousOn
  refine ⟨x,ax,y,ay,?_⟩
  by_contra! small
  let a := (θ x+θ y)/2
  have pos (s : ℝ) (hs : s∈Icc 0 P) : 0<Real.cos (θ s-a) := by
    apply Real.cos_pos_of_mem_Ioo
    dsimp [a]
    have low : θ x≤θ s := l hs
    have high : θ s≤θ y := h hs
    exact ⟨by linarith only [low,small],by linarith only [high,small]⟩
  have ct : Continuous (fun s=>Real.cos (θ s-a)) := Real.continuous_cos.comp (cθ.sub continuous_const)
  have good := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f:=fun _ : ℝ=>0) (g:=fun s=>Real.cos (θ s-a)) pp continuous_const.continuousOn ct.continuousOn
    (fun s hs=>(pos s ⟨hs.1.le,hs.2⟩).le) ⟨x,ax,pos x ax⟩
  simp only [intervalIntegral.integral_zero,Real.cos_sub] at good
  rw [intervalIntegral.integral_add (f:=fun s=>Real.cos (θ s)*Real.cos a) (g:=fun s=>Real.sin (θ s)*Real.sin a) (((Real.continuous_cos.comp cθ).mul_const _).intervalIntegrable ..)
    (((Real.continuous_sin.comp cθ).mul_const _).intervalIntegrable ..),
    intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const,hx,hy] at good
  linarith

/-- Directional variation times bending energy for an actual closed tangent.
Nonzero turning multiplies the spatial cost by its square, and turning number
zero still carries one complete weighted excursion by displacement closure. -/
theorem closed_projected_cost {P : ℝ} {θ k : ℝ→ℝ} (m : ℤ) (pp : 0<P)
    (dθ : ∀s,HasDerivAt θ (k s) s) (ck : Continuous k)
    (twist : θ P=θ 0+(m:ℝ)*(2*Real.pi))
    (hx : (∫s in (0:ℝ)..P,Real.cos (θ s))=0)
    (hy : (∫s in (0:ℝ)..P,Real.sin (θ s))=0) :
    2*(max 1 |(m:ℝ)| * halfPeriodMass)^2 ≤
      ((∫s in (0:ℝ)..P,(k s)^2)/2)*(∫s in (0:ℝ)..P,|Real.cos (θ s)|) := by
  have cθ := continuous_iff_continuousAt.mpr fun s => (dθ s).continuousAt
  have cw : Continuous directionalWeight := Real.continuous_cos.abs.sqrt
  have wn (x : ℝ) : 0≤directionalWeight x := Real.sqrt_nonneg _
  have per : Function.Periodic directionalWeight Real.pi := by
    intro z; simp only [directionalWeight,Real.cos_add_pi,abs_neg]
  have mass : 0≤halfPeriodMass := intervalIntegral.integral_nonneg Real.pi_pos.le (fun z _=>wn z)
  let H := fun y=>∫z in θ 0..y,directionalWeight z
  have dh (z : ℝ) : HasDerivAt H (directionalWeight z) z :=
    intervalIntegral.integral_hasDerivAt_right (cw.intervalIntegrable ..) (cw.stronglyMeasurableAtFilter _ _) cw.continuousAt
  let v := fun s=>directionalWeight (θ s)*k s
  have cv : Continuous v := (cw.comp cθ).mul ck
  have deriv (s : ℝ) : HasDerivAt (H ∘ θ) (v s) s := (dh _).comp s (dθ s)
  have variation : 2*(max 1 |(m:ℝ)| * halfPeriodMass) ≤ ∫s in (0:ℝ)..P,|v s| := by
    by_cases hz : m=0
    · subst m
      simp only [Int.cast_zero,abs_zero,max_eq_left zero_le_one,one_mul] at *
      have ends : θ P=θ 0 := by simpa using twist
      obtain ⟨x,ax,y,ay,big⟩ := range_from_closure pp cθ hx hy
      have realV := doubled (g:=H ∘ θ) (b:=v) (by simp only [Function.comp_apply,ends]) deriv cv ax ay
      have join := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
        (cw.intervalIntegrable (θ 0) (θ x)) (cw.intervalIntegrable (θ x) (θ y))
      have part := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
        (cw.intervalIntegrable (θ x) (θ x+Real.pi)) (cw.intervalIntegrable (θ x+Real.pi) (θ y))
      have nn := intervalIntegral.integral_nonneg (μ:=volume) (f:=directionalWeight) big (fun z _=>wn z)
      have shift := per.intervalIntegral_add_eq (θ x) 0
      simp only [zero_add] at shift
      have ord := le_abs_self ((H ∘ θ) y-(H ∘ θ) x)
      dsimp [Function.comp_def,H,halfPeriodMass] at *
      linarith only [realV,join,part,nn,shift,ord]
    · have h1 : (1:ℝ)≤|(m:ℝ)| := by exact_mod_cast Int.one_le_abs hz
      rw [max_eq_right h1]
      have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=P)
        (fun s _=>deriv s) (cv.intervalIntegrable ..)
      simp only [Function.comp_apply,H,intervalIntegral.integral_same,sub_zero] at eq
      have sh := per.intervalIntegral_add_zsmul_eq (2*m) (θ 0) (fun a b => cw.intervalIntegrable a b)
      have shift := per.intervalIntegral_add_eq (θ 0) 0
      simp only [zsmul_eq_mul,Int.cast_mul,Int.cast_ofNat,shift,zero_add] at sh
      rw [twist,show (m:ℝ)*(2*Real.pi)=2*(m:ℝ)*Real.pi by ring,sh] at eq
      change (∫s in (0:ℝ)..P,v s)=2*(m:ℝ)*halfPeriodMass at eq
      have bd := intervalIntegral.abs_integral_le_integral_abs (μ:=volume) (f:=v) pp.le
      rw [eq,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_of_nonneg mass] at bd
      linarith only [bd]
  have ident (s : ℝ) : |v s|=|k s| * directionalWeight (θ s) := by
    dsimp only [v]; rw [abs_mul,abs_of_nonneg (wn _)]; ring
  simp_rw [ident] at variation
  have cs := Flow.interval_integral_mul_sq_le ck.abs (cw.comp cθ) pp.le
  simp only [sq_abs,Function.comp_apply,directionalWeight,Real.sq_sqrt (abs_nonneg _)] at cs
  have s2 := pow_le_pow_left₀ (show 0≤2*(max 1 |(m:ℝ)| * halfPeriodMass) by positivity) variation 2
  unfold directionalWeight at s2
  linarith only [s2,cs]

end MigrationGeometry.AngularExcursion
#print axioms MigrationGeometry.AngularExcursion.closed_projected_cost
#print axioms MigrationGeometry.AngularExcursion.weighted_excursion
#print axioms MigrationGeometry.AngularExcursion.semicircle
