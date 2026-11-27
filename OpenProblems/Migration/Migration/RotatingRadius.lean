import Migration.RotatingHullDisk

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Rotating.UnitLoop
variable {L : ℝ} (c : UnitLoop L)

private theorem trace_mass_cap {M : ℝ} (lp : 0≤L) (cap : ∀s∈Icc 0 L,c.radialSq 0 s≤M) :
    mass (L:=L) (c.p 0)+mass (L:=L) (c.q 0)≤L*M := by
  have id (s : ℝ) : c.p 0 s^2+c.q 0 s^2=c.radialSq 0 s := by
    simp only [p,q,normalSupport,tangentSupport,Pi.zero_apply,sub_zero,radialSq]
    linear_combination (c.x s^2+c.y s^2)*c.unit s
  have ci := ((c.contP 0).pow 2).add ((c.contQ 0).pow 2)
  have bound := intervalIntegral.integral_mono_on lp (ci.intervalIntegrable (μ:=volume) 0 L)
    (g:=fun (_:ℝ) => M) (continuous_const.intervalIntegrable ..) (fun s hs => (id s).le.trans (cap s hs))
  change (∫s in (0:ℝ)..L,c.p 0 s^2+c.q 0 s^2)≤_ at bound
  rw [intervalIntegral.integral_add (f:=fun s=>c.p 0 s^2) (g:=fun s=>c.q 0 s^2)
    (((c.contP 0).pow 2).intervalIntegrable ..) (((c.contQ 0).pow 2).intervalIntegrable ..),
    intervalIntegral.integral_const,sub_zero,smul_eq_mul] at bound
  exact bound

/-- The tangential fraction of an exterior similarity profile satisfies
two coupled inequalities involving only its dimensionless squared radius
and its relative rotation. -/
theorem exterior_tangential_fraction {a b M : ℝ} (ap : 0<a) (lp : 0<L)
    (sol : c.IsRotating a b) (Mn : 0≤M) (cap : ∀s∈Icc 0 L,c.radialSq 0 s≤M)
    (out : (0:ℂ) ∉ convexHull ℝ c.traceSet) :
    let y := M*Real.sqrt (2*a)
    ∃ x : ℝ, 0<x ∧ 1+(1+b^2)*x≤y ∧ (1+b^2*x)^2<(Real.pi/2)^2*y^2*x := by
  let Z := mass (L:=L) (c.mixed b)
  let Q := mass (L:=L) (c.q 0)
  let t := Real.sqrt (2*a)
  let y := M*t
  obtain ⟨fk,fp,cs,zp⟩ := c.balances ap lp sol
  change 0<Z at zp
  have ts : t^2=2*a := Real.sq_sqrt (by linarith only [ap])
  have lz : L≤t*Z := by
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) zp.le)
    rw [mul_pow,ts]
    rw [fk] at cs
    change L^2≤2*a*Z*Z at cs
    nlinarith only [cs]
  have tr := c.trace_mass_cap lp.le cap
  rw [fp] at tr
  change Z+b^2*Q+Q≤L*M at tr
  have tm : Z+(1+b^2)*Q≤y*Z := by
    dsimp only [y]
    nlinarith only [tr,mul_le_mul_of_nonneg_right lz Mn]
  obtain ⟨A,B,unit,sep⟩ := c.exterior_separator lp out
  have co : coords 0=0 := by funext i; fin_cases i <;> rfl
  rw [co] at sep
  obtain ⟨m,h,hn,ht,osc⟩ := c.half_aperture lp unit sep
  have both := c.polar_mass_bound lp unit sep cap osc
  rw [fk,fp] at both
  change (Z+b^2*Q)^2≤M^2*h^2*(2*a*Z)*Q at both
  have qn : 0≤Q := intervalIntegral.integral_nonneg lp.le (fun _ _ => sq_nonneg _)
  have qp : 0<Q := lt_of_le_of_ne qn (by
    intro bad
    rw [← bad] at both
    simp only [mul_zero,add_zero,not_le.mpr (sq_pos_of_pos zp)] at both)
  have Mne := (c.exterior_pitch_bound ap lp sol unit sep cap osc).2
  have hsq : h^2<(Real.pi/2)^2 := by
    have sum := add_pos_of_pos_of_nonneg (div_pos Real.pi_pos (by norm_num : (0:ℝ)<2)) hn
    nlinarith only [mul_pos (sub_pos.mpr ht) sum]
  have ym : y^2=M^2*(2*a) := by dsimp only [y]; rw [mul_pow,ts]
  have pos := mul_pos (mul_pos (sq_pos_of_ne_zero Mne) (by linarith only [ap] : 0<2*a)) (mul_pos zp qp)
  have strict : (Z+b^2*Q)^2<(Real.pi/2)^2*y^2*(Q*Z) := by
    rw [ym]
    nlinarith only [both,mul_lt_mul_of_pos_right hsq pos]
  refine ⟨Q/Z,div_pos qp zp,?_,?_⟩
  · change 1+(1+b^2)*(Q/Z)≤y
    calc
      _ = (Z+(1+b^2)*Q)/Z := by field_simp [zp.ne']
      _ ≤ y := (div_le_iff₀ zp).mpr tm
  · change (1+b^2*(Q/Z))^2<(Real.pi/2)^2*y^2*(Q/Z)
    calc
      _ = (Z+b^2*Q)^2/Z^2 := by field_simp [zp.ne']
      _ < ((Real.pi/2)^2*y^2*(Q*Z))/Z^2 := (div_lt_div_iff_of_pos_right (sq_pos_of_pos zp)).mpr strict
      _ = _ := by field_simp [zp.ne']

/-- This radius exclusion remains effective even for zero relative rotation. -/
theorem center_mem_hull_of_small_radius {a b M : ℝ} (ap : 0<a) (lp : 0<L)
    (sol : c.IsRotating a b) (Mn : 0≤M) (cap : ∀s∈Icc 0 L,c.radialSq 0 s≤M)
    (small : let y := M*Real.sqrt (2*a); Real.pi^2*y^2*(y-1)≤4*(1+b^2)) :
    (0:ℂ) ∈ convexHull ℝ c.traceSet := by
  by_contra out
  let y := M*Real.sqrt (2*a)
  obtain ⟨x,xp,trace,angle⟩ := c.exterior_tangential_fraction ap lp sol Mn cap out
  change 1+(1+b^2)*x≤y at trace
  change (1+b^2*x)^2<(Real.pi/2)^2*y^2*x at angle
  change Real.pi^2*y^2*(y-1)≤4*(1+b^2) at small
  have low : 1≤(1+b^2*x)^2 := by
    have hx := mul_nonneg (sq_nonneg b) xp.le
    nlinarith only [hx,sq_nonneg (b^2*x)]
  have large : 4<Real.pi^2*y^2*x := by nlinarith only [lt_of_le_of_lt low angle]
  have hi := mul_lt_mul_of_pos_right large (show 0<1+b^2 by positivity)
  have bd := mul_le_mul_of_nonneg_left (show (1+b^2)*x≤y-1 by linarith only [trace])
    (mul_nonneg (sq_nonneg Real.pi) (sq_nonneg y))
  nlinarith only [hi,bd,small]

/-- The sharp elimination of the tangential fraction in the branch where
the trace cap is reached before the minimum of (1+b^2 x)/sqrt(x). -/
theorem center_mem_hull_of_coupled_radius {a b M : ℝ} (ap : 0<a) (lp : 0<L)
    (sol : c.IsRotating a b) (Mn : 0≤M) (cap : ∀s∈Icc 0 L,c.radialSq 0 s≤M)
    (branch : b^2*(M*Real.sqrt (2*a)-2)≤1)
    (small : let y := M*Real.sqrt (2*a)
             Real.pi^2*y^2*(y-1)*(1+b^2)≤4*(1+b^2*y)^2) :
    (0:ℂ) ∈ convexHull ℝ c.traceSet := by
  by_contra out
  let y := M*Real.sqrt (2*a)
  let u := b^2
  let g := y-1
  let C := 1+u
  have un : 0≤u := sq_nonneg b
  have Cp : 0<C := by dsimp [C,u]; positivity
  obtain ⟨x,xp,trace,angle⟩ := c.exterior_tangential_fraction ap lp sol Mn cap out
  change 1+C*x≤y at trace
  change (1+u*x)^2<(Real.pi/2)^2*y^2*x at angle
  change u*(y-2)≤1 at branch
  change Real.pi^2*y^2*g*C≤4*(1+u*y)^2 at small
  have gx : C*x≤g := by dsimp only [g]; linarith only [trace]
  have gp : 0<g := lt_of_lt_of_le (mul_pos Cp xp) gx
  have bc : u*g≤C := by dsimp only [g,C]; linarith only [branch]
  have xu : u*x≤1 := by
    apply le_of_mul_le_mul_right (a:=C) _ Cp
    nlinarith only [mul_le_mul_of_nonneg_left gx un,bc]
  have cmp : u^2*x*g≤C := by
    have h := mul_le_mul_of_nonneg_right xu (mul_nonneg un gp.le)
    nlinarith only [h,bc]
  have fact : x*(1+u*y)^2≤g*C*(1+u*x)^2 := by
    have f := mul_nonneg (sub_nonneg.mpr gx) (sub_nonneg.mpr cmp)
    have v : 1+u*y=C+u*g := by dsimp only [C,g]; ring
    rw [v]
    nlinarith only [f]
  have st := mul_lt_mul_of_pos_left angle (mul_pos gp Cp)
  have fin := mul_le_mul_of_nonneg_right small xp.le
  nlinarith only [fact,st,fin]

end MigrationGeometry.Rotating.UnitLoop
#print axioms MigrationGeometry.Rotating.UnitLoop.exterior_tangential_fraction
#print axioms MigrationGeometry.Rotating.UnitLoop.center_mem_hull_of_small_radius
#print axioms MigrationGeometry.Rotating.UnitLoop.center_mem_hull_of_coupled_radius
