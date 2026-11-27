import Migration.RotatingSupportBalance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Rotating.UnitLoop
variable {L : ℝ} (c : UnitLoop L)

def forward (d : Fin 2 → ℝ) (A B s : ℝ) := A*(c.x s-d 0)+B*(c.y s-d 1)
def side (d : Fin 2 → ℝ) (A B s : ℝ) := -B*(c.x s-d 0)+A*(c.y s-d 1)
def radialSq (d : Fin 2 → ℝ) (s : ℝ) := (c.x s-d 0)^2+(c.y s-d 1)^2
def angle (d : Fin 2 → ℝ) (A B s : ℝ) := Real.arctan (c.side d A B s/c.forward d A B s)

theorem angleD {d : Fin 2 → ℝ} {A B s : ℝ} (unit : A^2+B^2=1)
    (sep : 0<c.forward d A B s) :
    HasDerivAt (c.angle d A B) (-(c.p d s)/c.radialSq d s) s := by
  let U := c.forward d A B
  let V := c.side d A B
  let X := c.x s-d 0
  let Y := c.y s-d 1
  let dx := deriv c.x s
  let dy := deriv c.y s
  have xd := (c.hx.differentiable (by simp) s).hasDerivAt.sub_const (d 0)
  have yd := (c.hy.differentiable (by simp) s).hasDerivAt.sub_const (d 1)
  have ud : HasDerivAt U (A*dx+B*dy) s := (xd.const_mul A).add (yd.const_mul B)
  have vd : HasDerivAt V (-B*dx+A*dy) s := (xd.const_mul (-B)).add (yd.const_mul A)
  have us : U s ≠ 0 := sep.ne'
  have sq : U s^2+V s^2=c.radialSq d s := by
    dsimp only [U,V,forward,side,radialSq]
    linear_combination ((c.x s-d 0)^2+(c.y s-d 1)^2)*unit
  have vp : 0<c.radialSq d s := by rw [← sq]; positivity
  have cross : (-B*dx+A*dy)*U s-V s*(A*dx+B*dy)= -(c.p d s) := by
    dsimp only [U,V,forward,side,p,normalSupport,dx,dy]
    linear_combination ((c.x s-d 0)*deriv c.y s-(c.y s-d 1)*deriv c.x s)*unit
  apply ((vd.div ud us).arctan).congr_deriv
  change 1/(1+(V s/U s)^2)*(((-B*dx+A*dy)*U s-V s*(A*dx+B*dy))/U s^2)=_
  rw [cross,show 1+(V s/U s)^2=c.radialSq d s/U s^2 by rw [← sq]; field_simp [us]]
  field_simp [us,vp.ne']

theorem angle_periodic (d : Fin 2 → ℝ) (A B : ℝ) : Function.Periodic (c.angle d A B) L := by
  intro s
  simp only [angle,forward,side,c.px s,c.py s]

/-- A closed curve strictly in a viewing half-plane obeys a polar integral
bound. M bounds squared distance; h bounds the centred viewing angle. -/
theorem polar_mass_bound {d : Fin 2 → ℝ} {A B m h M : ℝ} (lp : 0<L)
    (unit : A^2+B^2=1) (sep : ∀s,0<c.forward d A B s)
    (cap : ∀s∈Icc 0 L,c.radialSq d s≤M)
    (osc : ∀s∈Icc 0 L,|c.angle d A B s-m|≤h) :
    (mass (L:=L) (c.p d))^2 ≤ M^2*h^2*mass (L:=L) c.k*mass (L:=L) (c.q d) := by
  let ψ := fun s => c.angle d A B s-m
  let p := c.p d
  let q := c.q d
  let v := c.radialSq d
  let t := fun s => (p s)^2/v s
  have vp (s) : 0<v s := by
    have u := sep s
    by_contra! bad
    have both : (c.x s-d 0)=0 ∧ (c.y s-d 1)=0 := by
      change (c.x s-d 0)^2+(c.y s-d 1)^2≤0 at bad
      constructor <;> nlinarith only [bad,sq_nonneg (c.x s-d 0),sq_nonneg (c.y s-d 1)]
    simp [forward,both.1,both.2] at u
  have cp : Continuous p := c.contP d
  have cq : Continuous q := c.contQ d
  have cv : Continuous v := ((c.hx.continuous.sub continuous_const).pow 2).add
    ((c.hy.continuous.sub continuous_const).pow 2)
  have ct : Continuous t := (cp.pow 2).div cv (fun s => (vp s).ne')
  have cψ : Continuous ψ := continuous_iff_continuousAt.mpr fun s =>
    ((c.angleD unit (sep s)).sub_const m).continuousAt
  have ci := c.contK.mul (cq.mul cψ)
  have hd (s) : HasDerivAt (fun u => p u*ψ u) (-(c.k s*(q s*ψ s))-t s) s := by
    apply ((c.pD d s).mul ((c.angleD unit (sep s)).sub_const m)).congr_deriv
    dsimp only [t,p,q,ψ,v]; ring
  have ident := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=L) (fun s _ => hd s)
    ((ci.neg.sub ct).intervalIntegrable ..)
  have perP := c.perP d 0
  have perA := c.angle_periodic d A B 0
  simp only [zero_add] at perP perA
  change (∫s in (0:ℝ)..L, -(c.k s*(q s*ψ s))-t s) = p L*ψ L-p 0*ψ 0 at ident
  rw [intervalIntegral.integral_sub (f:=fun s => -(c.k s*(q s*ψ s))) (g:=t)
    (ci.neg.intervalIntegrable ..) (ct.intervalIntegrable ..),intervalIntegral.integral_neg] at ident
  have ie : (∫s in (0:ℝ)..L,c.k s*(q s*ψ s))= -(∫s in (0:ℝ)..L,t s) := by
    dsimp only [p,ψ] at ident
    rw [perP,perA,sub_self] at ident
    linarith only [ident]
  have sqp : mass (L:=L) p ≤ M*(∫s in (0:ℝ)..L,t s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on lp.le ((cp.pow 2).intervalIntegrable ..) ((ct.const_mul M).intervalIntegrable ..)
    intro s hs
    have hp : 0≤t s := div_nonneg (sq_nonneg _) (vp s).le
    calc
      _ = v s*t s := by dsimp [t]; field_simp [(vp s).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (cap s hs) hp
  have sqψ : mass (L:=L) (fun s => q s*ψ s) ≤ h^2*mass (L:=L) q := by
    unfold mass
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on lp.le (((cq.mul cψ).pow 2).intervalIntegrable ..)
      (((cq.pow 2).const_mul (h^2)).intervalIntegrable ..)
    intro s hs
    have bd := osc s hs
    change |ψ s|≤h at bd
    have hsq := pow_le_pow_left₀ (abs_nonneg (ψ s)) bd 2
    rw [sq_abs] at hsq
    change (q s*ψ s)^2 ≤ h^2*q s^2
    simpa only [mul_pow,mul_comm (q s^2) _] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (q s))
  have cs := Flow.interval_integral_mul_sq_le c.contK (cq.mul cψ) lp.le
  change (∫s in (0:ℝ)..L,c.k s*(q s*ψ s))^2≤mass (L:=L) c.k*mass (L:=L) (fun s => q s*ψ s) at cs
  rw [ie,neg_sq] at cs
  have mn (f : ℝ → ℝ) : 0≤mass (L:=L) f := intervalIntegral.integral_nonneg lp.le (fun _ _ => sq_nonneg _)
  calc
    _ ≤ (M*(∫s in (0:ℝ)..L,t s))^2 := pow_le_pow_left₀ (mn _) sqp 2
    _ ≤ M^2*(mass (L:=L) c.k*(h^2*mass (L:=L) q)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (cs.trans (mul_le_mul_of_nonneg_left sqψ (mn _))) (sq_nonneg M)
    _ = _ := by ring

end MigrationGeometry.Rotating.UnitLoop
#print axioms MigrationGeometry.Rotating.UnitLoop.polar_mass_bound
