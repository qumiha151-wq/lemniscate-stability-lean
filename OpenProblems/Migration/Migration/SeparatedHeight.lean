import Migration.ExpanderCenterHull
import Migration.CurveKinematics
import Migration.SupportVirial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Perimeter obstruction for a pure expanding profile separated from its centre. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.SeparatedHeight

private theorem center_range {L : ℝ} {t B : ℝ → ℝ}
    (ct : Continuous t) (cB : Continuous B) (pB : ∀ x, 0 < B x)
    (spread : ∃ x ∈ Icc 0 L, ∃ y ∈ Icc 0 L, t y < t x) :
    ∃ l M : ℝ, 0 < M ∧
      (∀ s ∈ Icc 0 L, |(t s-l)/B s| ≤ M) ∧
      (∃ x ∈ Icc 0 L, (t x-l)/B x=M) ∧ (∃ y ∈ Icc 0 L, (t y-l)/B y= -M) := by
  let I := Icc 0 L
  let D := fun z : ℝ × ℝ => (t z.1-t z.2)/(B z.1+B z.2)
  have cD : Continuous D := ((ct.comp continuous_fst).sub (ct.comp continuous_snd)).div
    ((cB.comp continuous_fst).add (cB.comp continuous_snd))
    (fun z => (add_pos (pB z.1) (pB z.2)).ne')
  obtain ⟨x,hx,y,hy,hxy⟩ := spread
  obtain ⟨⟨a,b⟩,hab,hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    (show (I ×ˢ I).Nonempty from ⟨(x,y),hx,hy⟩) cD.continuousOn
  let M := D (a,b)
  have hM := lt_of_lt_of_le (show 0 < D (x,y) from
    div_pos (sub_pos.mpr hxy) (add_pos (pB x) (pB y)))
    (hmax (show (x,y) ∈ I ×ˢ I from ⟨hx,hy⟩))
  have bound (i j : ℝ) (hi : i∈I) (hj : j∈I) : t i-t j ≤ M*(B i+B j) :=
    (div_le_iff₀ (add_pos (pB i) (pB j))).mp (hmax (show (i,j) ∈ I ×ˢ I from ⟨hi,hj⟩))
  have eq : t a-t b = M*(B a+B b) :=
    (div_eq_iff (add_pos (pB a) (pB b)).ne').mp rfl
  refine ⟨t a-M*B a,M,hM,?_,⟨a,hab.1,?_⟩,⟨b,hab.2,?_⟩⟩
  · intro s hs
    rw [abs_le, le_div_iff₀ (pB s), div_le_iff₀ (pB s)]
    constructor
    · linarith only [bound a s hab.1 hs]
    · linarith only [eq,bound s b hs hab.2]
  · apply (div_eq_iff (pB a).ne').mpr
    ring
  · apply (div_eq_iff (pB b).ne').mpr
    linarith only [eq]

private theorem variation {u v : ℝ → ℝ} {L a b : ℝ}
    (hd : ∀ x, HasDerivAt u (v x) x) (cv : Continuous v) (ends : u L=u 0)
    (ha : a∈Icc 0 L) (hb : b∈Icc 0 L) :
    2*|u a-u b| ≤ ∫ s in 0..L, |v s| := by
  have bound (x y : ℝ) (hxy : x≤y) : |u y-u x| ≤ ∫ s in x..y, |v s| := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (cv.intervalIntegrable x y)]
    exact intervalIntegral.abs_integral_le_integral_abs hxy
  have ordered (x y : ℝ) (hx : 0≤x) (hxy : x≤y) (hy : y≤L) :
      2*|u x-u y| ≤ ∫ s in 0..L, |v s| := by
    have tri := abs_sub_le (u x) (u 0) (u y)
    have first := bound 0 x hx
    have middle := bound x y hxy
    have last := bound y L hy
    rw [ends] at last
    rw [abs_sub_comm] at middle
    have join := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (cv.abs.intervalIntegrable 0 x)
      (cv.abs.intervalIntegrable x y)
    have close := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (cv.abs.intervalIntegrable 0 y)
      (cv.abs.intervalIntegrable y L)
    linarith
  rcases le_total a b with hab | hba
  · exact ordered a b ha.1 hab hb.2
  · rw [abs_sub_comm]
    exact ordered b a hb.1 hba ha.2

private theorem strict_weighted_square {L a : ℝ} (hL : 0<L) {h v : ℝ → ℝ}
    (ch : Continuous h) (ph : ∀ s, 0<h s) (cv : Continuous v)
    (ha : a∈Icc 0 L) (va : v a=0) (tv : 0 < ∫ s in 0..L, |v s|) :
    (∫ s in 0..L, |v s|)^2 <
      (∫ s in 0..L, (h s)⁻¹^2)*(∫ s in 0..L, (h s)^2*(v s)^2) := by
  let I := ∫ s in 0..L, (h s)⁻¹^2
  let V := ∫ s in 0..L, |v s|
  have ci := (ch.inv₀ (fun s => (ph s).ne')).pow 2
  have ip : 0<I := by
    have p := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun _ : ℝ => (0:ℝ)) (g := fun s => (h s)⁻¹^2)
      hL continuous_const.continuousOn ci.continuousOn
      (fun s _ => sq_nonneg _) ⟨a,ha,sq_pos_of_pos (inv_pos.mpr (ph a))⟩
    simpa only [intervalIntegral.integral_zero] using p
  let k := V/I
  have kp : 0<k := div_pos tv ip
  let w := fun s => h s*|v s|-k*(h s)⁻¹
  have cw : Continuous w := (ch.mul cv.abs).sub ((ch.inv₀ (fun s => (ph s).ne')).const_mul k)
  have nonzero : w a≠0 := by
    dsimp [w]
    rw [va,abs_zero,mul_zero,zero_sub]
    exact neg_ne_zero.mpr (mul_pos kp (inv_pos.mpr (ph a))).ne'
  have p := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => (0:ℝ)) (g := fun s => w s^2) hL
    continuous_const.continuousOn (cw.pow 2).continuousOn
    (fun s _ => sq_nonneg _) ⟨a,ha,sq_pos_of_ne_zero nonzero⟩
  have identity : (fun s => w s^2) = fun s => h s^2*v s^2 - (2*k)*|v s|+k^2*((h s)⁻¹)^2 := by
    funext s
    dsimp only [w]
    have hs := (ph s).ne'
    rw [← sq_abs (v s)]
    field_simp
    ring
  simp only [intervalIntegral.integral_zero] at p
  rw [identity, intervalIntegral.integral_add
    (f := fun s => h s^2*v s^2 - (2*k)*|v s|) (g := fun s => k^2*((h s)⁻¹)^2)
    ((((ch.pow 2).mul (cv.pow 2)).sub (cv.abs.const_mul (2*k))).intervalIntegrable _ _)
    ((ci.const_mul (k^2)).intervalIntegrable _ _), intervalIntegral.integral_sub
    (f := fun s => h s^2*v s^2) (g := fun s => (2*k)*|v s|)
    (((ch.pow 2).mul (cv.pow 2)).intervalIntegrable _ _) ((cv.abs.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at p
  change 0 < _ - (2*k)*V+k^2*I at p
  have eq : k*I=V := div_mul_cancel₀ V ip.ne'
  change V^2<I*_
  nlinarith only [mul_pos ip p,eq,congrArg (fun q : ℝ => q*q) eq,
    congrArg (fun q : ℝ => q*V) eq]

/-- The normal-distance balance of a periodic unit-speed pair already forces
this strict estimate on every positive first coordinate. -/
theorem weighted_height {L : ℝ} (hL : 0<L) {h y H Y : ℝ → ℝ}
    (dh : ∀ s, HasDerivAt h (H s) s) (dy : ∀ s, HasDerivAt y (Y s) s)
    (cH : Continuous H) (cY : Continuous Y)
    (hp : Function.Periodic h L) (yp : Function.Periodic y L)
    (ph : ∀ s, 0<h s) (unit : ∀ s, H s^2+Y s^2=1)
    (balance : ∀ l : ℝ, (∫ s in 0..L, (h s*Y s-y s*H s)*(Y s-l*H s))=0) :
    64 < (∫ s in 0..L, (h s)⁻¹^2)*(∫ s in 0..L, H s^2) := by
  have ch := continuous_iff_continuousAt.mpr (fun s => (dh s).continuousAt)
  have cy := continuous_iff_continuousAt.mpr (fun s => (dy s).continuousAt)
  let t := fun s => y s/h s
  let B := fun s => (Real.sqrt (h s))⁻¹
  have ct : Continuous t := cy.div ch (fun s => (ph s).ne')
  have sp (s) : 0<Real.sqrt (h s) := Real.sqrt_pos.mpr (ph s)
  have cb : Continuous B := ch.sqrt.inv₀ (fun s => (sp s).ne')
  have he : h 0=h L := by simpa using (hp 0).symm
  have spread : ∃ x ∈ Icc 0 L, ∃ z ∈ Icc 0 L, t z < t x := by
    by_contra! hn
    have h0 : (0:ℝ)∈Icc 0 L := ⟨le_rfl,hL.le⟩
    have tp : Function.Periodic t L := yp.div hp
    have eq (s : ℝ) : y s=t 0*h s := by
      obtain ⟨z,hz,hz'⟩ := tp.exists_mem_Ico₀ hL s
      have mem : z∈Icc 0 L := ⟨hz.1,hz.2.le⟩
      apply (div_eq_iff (ph s).ne').mp
      change t s = t 0
      exact hz'.trans (le_antisymm (hn z mem 0 h0) (hn 0 h0 z mem))
    obtain ⟨z,_,hz⟩ := exists_hasDerivAt_eq_zero hL ch.continuousOn he (fun s _ => dh s)
    have hy' : Y z=t 0*H z := (dy z).unique (((dh z).const_mul (t 0)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall eq))
    have hu := unit z
    rw [hy',hz] at hu
    norm_num at hu
  obtain ⟨l,M,hM,bound,⟨a,ha,va⟩,⟨b,hb,vb⟩⟩ := center_range ct cb
    (fun s => inv_pos.mpr (sp s)) spread
  let f := fun s => y s-l*h s
  let F := fun s => Y s-l*H s
  let g := fun s => Real.sqrt (h s)
  let u := fun s => f s/g s
  let v := fun s => (F s*g s-f s*(H s/(2*g s)))/(g s)^2
  have gg (s) : g s^2=h s := Real.sq_sqrt (ph s).le
  have gf (s) : HasDerivAt g (H s/(2*g s)) s := (dh s).sqrt (ph s).ne'
  have ff (s) : HasDerivAt f (F s) s := (dy s).sub ((dh s).const_mul l)
  have du (s) : HasDerivAt u (v s) s := (ff s).div (gf s) (sp s).ne'
  have cu := continuous_iff_continuousAt.mpr (fun s => (du s).continuousAt)
  have cf : Continuous f := cy.sub (ch.const_mul l)
  have cF : Continuous F := cY.sub (cH.const_mul l)
  have cg : Continuous g := ch.sqrt
  have cv : Continuous v := ((cF.mul cg).sub (cf.mul (cH.div (cg.const_mul 2)
    (fun s => (mul_pos (by norm_num) (sp s)).ne')))).div (cg.pow 2)
    (fun s => pow_ne_zero _ (sp s).ne')
  have repr (s) : (t s-l)/B s = u s := by
    dsimp only [t,B,u,f]
    change (y s/h s-l)/(g s)⁻¹ = (y s-l*h s)/g s
    rw [div_inv_eq_mul, ← gg s]
    have hs : g s ≠ 0 := (sp s).ne'
    field_simp [hs]
  simp only [repr] at bound va vb
  have ends : u L=u 0 := by simp only [u,f,g,he.symm,
    show y L=y 0 by simpa using yp 0]
  have lower := variation du cv ends ha hb
  rw [va,vb,sub_neg_eq_add,abs_of_pos (add_pos hM hM)] at lower
  obtain ⟨z,hz,dz⟩ := exists_hasDerivAt_eq_zero hL cu.continuousOn ends.symm (fun s _ => du s)
  have strict := strict_weighted_square hL ch ph cv ⟨hz.1.le,hz.2.le⟩ dz (by linarith)
  have eq (s) : 4*(h s^2*v s^2) = H s^2*u s^2 +
      4*((h s*Y s-y s*H s)*F s) := by
    dsimp only [u,v,f,F]
    rw [← gg s]
    have hs : g s ≠ 0 := (sp s).ne'
    field_simp [hs]
    ring
  have virial : 4*(∫ s in 0..L, h s^2*v s^2) = ∫ s in 0..L, H s^2*u s^2 := by
    have e := congrArg (fun (f : ℝ → ℝ) => ∫ s in 0..L, f s) (funext eq)
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
      (f := fun s => H s^2*u s^2) (g := fun s => 4*((h s*Y s-y s*H s)*F s))
      (((cH.pow 2).mul (cu.pow 2)).intervalIntegrable _ _)
      (((((ch.mul cY).sub (cy.mul cH)).mul cF).const_mul 4).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, show (∫ s in 0..L, (h s*Y s-y s*H s)*F s)=0
        from balance l, mul_zero,add_zero] at e
    exact e
  have boundI := intervalIntegral.integral_mono_on (μ := volume) hL.le
    (((cH.pow 2).mul (cu.pow 2)).intervalIntegrable 0 L)
    (((cH.pow 2).const_mul (M^2)).intervalIntegrable 0 L) (fun s hs =>
      show H s^2*u s^2 ≤ M^2*H s^2 by
        rw [mul_comm (M^2)]
        exact mul_le_mul_of_nonneg_left ((sq_le_sq).mpr (by simpa [abs_of_pos hM] using bound s hs))
          (sq_nonneg _))
  change (∫ s in 0..L, H s^2*u s^2) ≤ ∫ s in 0..L, M^2*H s^2 at boundI
  rw [intervalIntegral.integral_const_mul,← virial] at boundI
  have ip : 0≤ ∫ s in 0..L, (h s)⁻¹^2 :=
    intervalIntegral.integral_nonneg hL.le (fun s _ => sq_nonneg _)
  have tbound : (4*M)^2 ≤ (∫ s in 0..L, |v s|)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  by_contra! fail
  nlinarith only [tbound,strict,mul_le_mul_of_nonneg_left boundI ip,
    mul_le_mul_of_nonneg_left fail (sq_nonneg M)]

end MigrationGeometry.SeparatedHeight

namespace MigrationGeometry.Adjoint.ClosedExpander

/-- Every strictly separating unit direction of a true pure homothety
satisfies a strict, energy-independent integral bound. -/
theorem separated_height_weighted {rate L a b : ℝ} (c : ClosedExpander rate L)
    (hr : 0<rate) (hL : 0<L) (he : a^2+b^2=1)
    (pos : ∀ s, 0<a*c.x s+b*c.y s) :
    64 < (∫ s in 0..L, (a*c.x s+b*c.y s)⁻¹^2)*
      (∫ s in 0..L, (a*deriv c.x s+b*deriv c.y s)^2) := by
  let h := fun s => a*c.x s+b*c.y s
  let y := fun s => -b*c.x s+a*c.y s
  let H := fun s => a*deriv c.x s+b*deriv c.y s
  let Y := fun s => -b*deriv c.x s+a*deriv c.y s
  let D := fun s => c.x s*deriv c.y s-c.y s*deriv c.x s
  have hx (s) := (c.hx.differentiable (by simp) s).hasDerivAt
  have hy (s) := (c.hy.differentiable (by simp) s).hasDerivAt
  have cx := (contDiff_infty_iff_deriv.mp c.hx).2.continuous
  have cy := (contDiff_infty_iff_deriv.mp c.hy).2.continuous
  apply MigrationGeometry.SeparatedHeight.weighted_height hL (y := y) (Y := Y)
    (h := h) (H := H)
    (fun s => ((hx s).const_mul a).add ((hy s).const_mul b))
    (fun s => ((hx s).const_mul (-b)).add ((hy s).const_mul a))
    ((cx.const_mul a).add (cy.const_mul b)) ((cx.const_mul (-b)).add (cy.const_mul a))
    (fun s => by simp only [h,c.px s,c.py s]) (fun s => by simp only [y,c.px s,c.py s]) pos
  · intro s
    dsimp [H,Y]
    linear_combination (a^2+b^2)*c.unit s+he
  · intro l
    have id (s) : h s*Y s-y s*H s=D s := by
      dsimp [h,y,H,Y,D]
      linear_combination (c.x s*deriv c.y s-c.y s*deriv c.x s)*he
    let F := elasticForce c.x c.y
    have hf (s) : F s=rate*D s := by
      have eq := c.profile s
      simp only [normalSupport,Pi.zero_apply,sub_zero] at eq
      dsimp [F,D]
      linarith only [eq]
    have eq (s) : rate*((h s*Y s-y s*H s)*(Y s-l*H s)) =
        (l*b-a)*(F s*(-deriv c.y s))+(-b-l*a)*(F s*deriv c.x s) := by
      rw [id,hf]
      dsimp [Y,H]
      ring
    have cf := (elasticForce_smooth c.hx c.hy).continuous
    have e := congrArg (fun (f : ℝ → ℝ) => ∫ s in 0..L, f s) (funext eq)
    have bal := elasticForce_balance c.hx c.hy c.px c.py c.unit
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
      (f := fun s => (l*b-a)*(F s*(-deriv c.y s))) (g := fun s => (-b-l*a)*(F s*deriv c.x s))
      (((cf.mul cy.neg).const_mul _).intervalIntegrable _ _)
      (((cf.mul cx).const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      show (∫ s in 0..L, F s*(-deriv c.y s))=0 from bal.1,
      show (∫ s in 0..L, F s*deriv c.x s)=0 from bal.2] at e
    exact (mul_eq_zero.mp (by simpa using e)).resolve_left hr.ne'

/-- The distance to every supporting line separating the actual centre from
the profile is strictly less than one eighth of the perimeter. -/
theorem separated_height_lt_eighth {rate L a b d : ℝ} (c : ClosedExpander rate L)
    (hr : 0<rate) (hL : 0<L) (he : a^2+b^2=1) (hd : 0<d)
    (lower : ∀ s, d≤a*c.x s+b*c.y s) : d<L/8 := by
  let h := fun s => a*c.x s+b*c.y s
  let H := fun s => a*deriv c.x s+b*deriv c.y s
  have ch : Continuous h := (c.hx.continuous.const_mul a).add (c.hy.continuous.const_mul b)
  have cH : Continuous H := ((contDiff_infty_iff_deriv.mp c.hx).2.continuous.const_mul a).add
    ((contDiff_infty_iff_deriv.mp c.hy).2.continuous.const_mul b)
  have pos (s) : 0<h s := hd.trans_le (lower s)
  have G := c.separated_height_weighted hr hL he pos
  change 64 < (∫ s in 0..L, (h s)⁻¹^2)*(∫ s in 0..L, H s^2) at G
  have I := intervalIntegral.integral_mono_on (μ := volume) hL.le
    (((ch.inv₀ (fun s => (pos s).ne')).pow 2).intervalIntegrable 0 L)
    (continuous_const.intervalIntegrable 0 L) (fun s _ =>
      show (h s)⁻¹^2≤d⁻¹^2 from
        pow_le_pow_left₀ (inv_pos.mpr (pos s)).le (inv_anti₀ hd (lower s)) 2)
  have J := intervalIntegral.integral_mono_on (μ := volume) hL.le
    ((cH.pow 2).intervalIntegrable 0 L) (continuous_const.intervalIntegrable 0 L)
    (fun s _ => show H s^2≤1 by
      dsimp [H]
      have norm : (a*deriv c.x s+b*deriv c.y s)^2+(-b*deriv c.x s+a*deriv c.y s)^2=1 := by
        linear_combination (a^2+b^2)*c.unit s+he
      linarith only [norm,sq_nonneg (-b*deriv c.x s+a*deriv c.y s)])
  change (∫ s in 0..L, (h s)⁻¹^2)≤ ∫ _ in (0:ℝ)..L, d⁻¹^2 at I
  change (∫ s in 0..L, H s^2)≤ ∫ _ in (0:ℝ)..L, (1:ℝ) at J
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at I J
  have B := lt_of_lt_of_le G (mul_le_mul I J (intervalIntegral.integral_nonneg hL.le
    (fun s _ => sq_nonneg (H s))) (by positivity))
  field_simp [hd.ne'] at B
  by_contra! bad
  nlinarith only [B,mul_nonneg (show 0≤8*d-L by linarith) (show 0≤8*d+L by positivity)]

#print axioms separated_height_weighted
#print axioms separated_height_lt_eighth

/-- If an actual dilation separates two slices across a line, its factor is
strictly greater than one plus eight times their earlier directional width
divided by the earlier perimeter. -/
theorem separated_slices_dilation {rate L a b ρ line lo hi : ℝ} (c : ClosedExpander rate L)
    (hr : 0<rate) (hL : 0<L) (he : a^2+b^2=1) (hρ : 1<ρ)
    (hlo : ∀ s, a*c.x lo+b*c.y lo≤a*c.x s+b*c.y s)
    (before : ∀ s, a*c.x s+b*c.y s<line)
    (after : ∀ s, line<ρ*(a*c.x s+b*c.y s)) :
    1+8*((a*c.x hi+b*c.y hi)-(a*c.x lo+b*c.y lo))/L<ρ := by
  let d := a*c.x lo+b*c.y lo
  let m := a*c.x hi+b*c.y hi
  have sep : m<ρ*d := (before hi).trans (after lo)
  have self : d<ρ*d := (before lo).trans (after lo)
  have pos : 0<d := by
    by_contra! hn
    nlinarith only [self,mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hρ.le) hn]
  have cap := c.separated_height_lt_eighth hr hL he pos hlo
  change 1+8*(m-d)/L<ρ
  rw [← lt_sub_iff_add_lt',div_lt_iff₀ hL]
  nlinarith only [sep,mul_pos (sub_pos.mpr hρ) (show 0<L-8*d by linarith)]

#print axioms separated_slices_dilation

private theorem rate_perimeter {rate L : ℝ} (c : ClosedExpander rate L)
    (hr : 0<rate) (hL : 0<L) : rate*L^2 ≤ 2*(bendingEnergy c.x c.y L)^2 := by
  let p := normalSupport c.x c.y 0
  have vir := elasticForce_normalSupport_integral c.hx c.hy c.px c.py c.unit 0
  have val : (∫ s in 0..L, elasticForce c.x c.y s * p s) =
      -rate*(∫ s in 0..L, p s^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    change elasticForce c.x c.y s*p s = -rate*p s^2
    rw [c.profile]
    change -rate*p s*p s= -rate*p s^2
    ring
  change (∫ s in 0..L, elasticForce c.x c.y s*p s)=_ at vir
  rw [val] at vir
  have cs := MigrationGeometry.Flow.interval_integral_mul_sq_le
    (signedCurvature_smooth c.hx c.hy).continuous (normalSupport_continuous c.hx c.hy 0) hL.le
  rw [curvature_normalSupport_integral c.hx c.hy c.px c.py c.unit 0] at cs
  change (-L)^2 ≤ (∫ s in 0..L, signedCurvature c.x c.y s^2)*(∫ s in 0..L, p s^2) at cs
  let E := bendingEnergy c.x c.y L
  have ee : (∫ s in 0..L, signedCurvature c.x c.y s^2)=2*E := by
    dsimp [E,bendingEnergy]
    ring
  rw [ee] at cs
  change -rate*_ = -E at vir
  change rate*L^2≤2*E^2
  nlinarith only [mul_le_mul_of_nonneg_left cs hr.le,congrArg (fun q : ℝ => q*E) vir]

/-- Time cost for a separated expansion with the fourth-power scaling law. -/
theorem separated_slices_elapsed {rate L a b ρ line lo hi dt : ℝ} (c : ClosedExpander rate L)
    (hr : 0<rate) (hL : 0<L) (he : a^2+b^2=1) (hρ : 1<ρ)
    (hlo : ∀ s, a*c.x lo+b*c.y lo≤a*c.x s+b*c.y s)
    (before : ∀ s, a*c.x s+b*c.y s<line)
    (after : ∀ s, line<ρ*(a*c.x s+b*c.y s))
    (hdt : 0≤dt) (scale : ρ^4=1+4*rate*dt) :
    L^2*((1+8*((a*c.x hi+b*c.y hi)-(a*c.x lo+b*c.y lo))/L)^4-1)/
      (8*(bendingEnergy c.x c.y L)^2)<dt := by
  let B := 1+8*((a*c.x hi+b*c.y hi)-(a*c.x lo+b*c.y lo))/L
  have pos : 0≤B := by
    dsimp [B]
    have := sub_nonneg.mpr (hlo hi)
    positivity
  have gap : B<ρ := c.separated_slices_dilation hr hL he hρ hlo before after
  have fourth := pow_lt_pow_left₀ gap pos (show 4≠0 by decide)
  rw [scale] at fourth
  let E := bendingEnergy c.x c.y L
  have ep : 0<E := bendingEnergy_pos c.hx c.hy hL c.px c.py c.unit
  change L^2*(B^4-1)/(8*E^2)<dt
  apply (div_lt_iff₀ (by positivity)).mpr
  have cap := c.rate_perimeter hr hL
  change rate*L^2≤2*E^2 at cap
  nlinarith only [mul_lt_mul_of_pos_left (show B^4-1<4*rate*dt by linarith)
    (sq_pos_of_pos hL),mul_le_mul_of_nonneg_right cap hdt]

#print axioms separated_slices_elapsed
end MigrationGeometry.Adjoint.ClosedExpander
