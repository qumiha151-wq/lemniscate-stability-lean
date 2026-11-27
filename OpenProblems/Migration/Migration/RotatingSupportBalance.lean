import Migration.PhysicalViewingAngle

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Rotating

/-- A unit-speed closed immersion in Cartesian coordinates, based at an
arbitrary origin. Its distinguished expansion centre, when used, is zero. -/
structure UnitLoop (L : ℝ) where
  x : ℝ → ℝ
  y : ℝ → ℝ
  hx : ContDiff ℝ ∞ x
  hy : ContDiff ℝ ∞ y
  px : Function.Periodic x L
  py : Function.Periodic y L
  unit (s : ℝ) : (deriv x s)^2+(deriv y s)^2=1

namespace UnitLoop
variable {L : ℝ} (c : UnitLoop L)
abbrev k := signedCurvature c.x c.y
abbrev p (d : Fin 2 → ℝ) := normalSupport c.x c.y d
abbrev q (d : Fin 2 → ℝ) := tangentSupport c.x c.y d
abbrev F := elasticForce c.x c.y
def mass (f : ℝ → ℝ) := ∫ s in (0:ℝ)..L, (f s)^2
def mixed (b : ℝ) (s : ℝ) := c.p 0 s+b*c.q 0 s
def IsRotating (a b : ℝ) : Prop := ∀ s, c.F s= -a*c.mixed b s

theorem pD (d : Fin 2 → ℝ) (s : ℝ) :
    HasDerivAt (c.p d) (-c.k s*c.q d s) s := by
  have := ((((c.hx.differentiable (by simp) s).hasDerivAt.sub_const (d 0)).neg.mul
    ((contDiff_infty_iff_deriv.mp c.hy).2.differentiable (by simp) s).hasDerivAt).add
    (((c.hy.differentiable (by simp) s).hasDerivAt.sub_const (d 1)).mul
      ((contDiff_infty_iff_deriv.mp c.hx).2.differentiable (by simp) s).hasDerivAt))
  apply this.congr_deriv
  rw [frenet_x c.hx c.hy c.unit s,frenet_y c.hx c.hy c.unit s]
  dsimp only [k,q,tangentSupport,Pi.neg_apply]
  ring

theorem qD (d : Fin 2 → ℝ) (s : ℝ) : HasDerivAt (c.q d) (1+c.k s*c.p d s) s :=
  tangentSupport_hasDerivAt c.hx c.hy c.unit d s

theorem contP (d : Fin 2 → ℝ) : Continuous (c.p d) := normalSupport_continuous c.hx c.hy d
theorem contQ (d : Fin 2 → ℝ) : Continuous (c.q d) :=
  continuous_iff_continuousAt.mpr fun s => (c.qD d s).continuousAt
theorem perP (d : Fin 2 → ℝ) : Function.Periodic (c.p d) L := by
  intro s
  simp only [p,normalSupport,c.px s,c.py s,periodic_actual_deriv c.px s,periodic_actual_deriv c.py s]
theorem contK : Continuous c.k := (signedCurvature_smooth c.hx c.hy).continuous
theorem contMixed (b : ℝ) : Continuous (c.mixed b) := (c.contP 0).add ((c.contQ 0).const_mul b)

private theorem torque :
    (∫s in (0:ℝ)..L,c.F s*c.q 0 s)=0 := by
  let K := c.k
  let q := c.q 0
  let p := c.p 0
  let H := fun s => q s*deriv K s-p s*(K s)^2/2-K s
  have hk : ContDiff ℝ ∞ K := signedCurvature_smooth c.hx c.hy
  have hor (s : ℝ) : HasDerivAt H (c.F s*q s) s := by
    have kd := (hk.differentiable (by simp) s).hasDerivAt
    have vd := ((contDiff_infty_iff_deriv.mp hk).2.differentiable (by simp) s).hasDerivAt
    apply ((((c.qD 0 s).mul vd).sub (((c.pD 0 s).mul (kd.pow 2)).div_const 2)).sub kd).congr_deriv
    dsimp only [q,p,K,k,F,elasticForce,Pi.pow_apply]; ring
  have perK : Function.Periodic K L := signedCurvature_periodic c.px c.py
  have perH : H L=H 0 := by
    have pp := c.perP 0 0
    have qp := tangentSupport_periodic c.px c.py (0:Fin 2 → ℝ) 0
    have kp := perK 0
    have vp := periodic_actual_deriv perK 0
    simp only [zero_add] at pp qp kp vp
    change c.q 0 L=c.q 0 0 at qp
    dsimp only [H,q,p]; rw [pp,qp,kp,vp]
  have id := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=L) (fun s _ => hor s)
    (((elasticForce_smooth c.hx c.hy).continuous.mul (c.contQ 0)).intervalIntegrable ..)
  simpa only [perH,sub_self] using id

/-- The rotation, dilation and curvature identities all use the actual force
and the actual tangent and normal supports of the given immersion. -/
theorem balances {a b : ℝ} (ha : 0<a) (hL : 0<L) (sol : c.IsRotating a b) :
    mass (L:=L) c.k=2*a*mass (L:=L) (c.mixed b) ∧
    mass (L:=L) (c.p 0)=mass (L:=L) (c.mixed b)+b^2*mass (L:=L) (c.q 0) ∧
    L^2≤mass (L:=L) c.k*mass (L:=L) (c.mixed b) ∧ 0<mass (L:=L) (c.mixed b) := by
  let z := c.mixed b
  let p := c.p 0
  let q := c.q 0
  have cz : Continuous z := c.contMixed b
  have cp : Continuous p := c.contP 0
  have cq : Continuous q := c.contQ 0
  have ck := c.contK
  have torque := c.torque
  have vir := elasticForce_normalSupport_integral c.hx c.hy c.px c.py c.unit (0:Fin 2 → ℝ)
  change (∫s in (0:ℝ)..L,c.F s*p s)= -(mass (L:=L) c.k/2) at vir
  have fe (s : ℝ) : c.F s= -a*z s := sol s
  simp_rw [fe] at torque vir
  simp only [mul_assoc,intervalIntegral.integral_const_mul] at torque vir
  have orth : (∫s in (0:ℝ)..L,z s*q s)=0 := (mul_eq_zero.mp torque).resolve_left (neg_ne_zero.mpr ha.ne')
  have zp : (∫s in (0:ℝ)..L,z s*p s)=mass (L:=L) z := by
    have eq (s : ℝ) : z s*p s=(z s)^2-b*(z s*q s) := by dsimp [z,mixed,p,q]; ring
    simp_rw [eq]
    rw [intervalIntegral.integral_sub (f:=fun s => z s^2) (g:=fun s => b*(z s*q s)) ((cz.pow 2).intervalIntegrable ..)
      (((cz.mul cq).const_mul b).intervalIntegrable ..),intervalIntegral.integral_const_mul,orth,mul_zero,sub_zero]
    rfl
  change -a*(∫s in (0:ℝ)..L,z s*p s)= -(mass (L:=L) c.k/2) at vir
  rw [zp] at vir
  have en : mass (L:=L) c.k=2*a*mass (L:=L) z := by linarith only [vir]
  have pp (s : ℝ) : p s^2=z s^2+b^2*(q s)^2-2*b*(z s*q s) := by dsimp [z,mixed,p,q]; ring
  have pMass : mass (L:=L) p=mass (L:=L) z+b^2*mass (L:=L) q := by
    unfold mass
    simp_rw [pp]
    rw [intervalIntegral.integral_sub (f:=fun s => z s^2+b^2*q s^2) (g:=fun s => 2*b*(z s*q s)) (((cz.pow 2).add ((cq.pow 2).const_mul (b^2))).intervalIntegrable ..)
        (((cz.mul cq).const_mul (2*b)).intervalIntegrable ..),
      intervalIntegral.integral_add (f:=fun s=>z s^2) (g:=fun s=>b^2*q s^2) ((cz.pow 2).intervalIntegrable ..) (((cq.pow 2).const_mul (b^2)).intervalIntegrable ..),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,orth,mul_zero,sub_zero]
  have pk := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=L) (fun s _ => c.pD 0 s)
    ((ck.neg.mul cq).intervalIntegrable ..)
  have pe := c.perP 0 0
  simp only [zero_add] at pe
  simp only [neg_mul,intervalIntegral.integral_neg,pe,sub_self,neg_eq_zero] at pk
  have kv := curvature_normalSupport_integral c.hx c.hy c.px c.py c.unit (0:Fin 2 → ℝ)
  have kz : (∫s in (0:ℝ)..L,c.k s*z s)= -L := by
    change (∫s in (0:ℝ)..L,c.k s*(p s+b*q s))= -L
    simp only [mul_add,show ∀s,c.k s*(b*q s)=b*(c.k s*q s) from fun s => by ring]
    rw [intervalIntegral.integral_add (f:=fun s=>c.k s*p s) (g:=fun s=>b*(c.k s*q s)) ((ck.mul cp).intervalIntegrable ..) (((ck.mul cq).const_mul b).intervalIntegrable ..),
      intervalIntegral.integral_const_mul]
    change (∫s in (0:ℝ)..L,c.k s*p s)+b*(∫s in (0:ℝ)..L,c.k s*c.q 0 s)= -L
    rw [pk,mul_zero,add_zero]; exact kv
  have cs := Flow.interval_integral_mul_sq_le ck cz hL.le
  rw [kz,neg_sq] at cs
  have ep := bendingEnergy_pos c.hx c.hy hL c.px c.py c.unit
  change 0<mass (L:=L) c.k/2 at ep
  exact ⟨en,pMass,cs,pos_of_mul_pos_right (by linarith only [ep,en] : 0<2*a*mass (L:=L) z) (by positivity)⟩

end UnitLoop
end MigrationGeometry.Rotating
#print axioms MigrationGeometry.Rotating.UnitLoop.balances
