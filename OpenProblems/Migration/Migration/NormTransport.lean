import Migration.RotatingHull

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Rotating.UnitLoop
variable {L : ℝ} (c : UnitLoop L)

def size (f : ℝ → ℝ) := Real.sqrt (mass (L:=L) f)

theorem size_sq (lp : 0≤L) (f : ℝ → ℝ) : size (L:=L) f^2=mass (L:=L) f :=
  Real.sq_sqrt (intervalIntegral.integral_nonneg lp (fun _ _ => sq_nonneg _))

theorem size_triangle {f g : ℝ→ℝ} (lp : 0≤L) (cf : Continuous f) (cg : Continuous g) :
    size (L:=L) (f+g) ≤ size (L:=L) f+size (L:=L) g := by
  let I := ∫ s in (0:ℝ)..L,f s*g s
  have cs := Flow.interval_integral_mul_sq_le cf cg lp
  change I^2≤mass (L:=L) f*mass (L:=L) g at cs
  rw [← size_sq lp f,← size_sq lp g,← mul_pow] at cs
  have cross : I≤size (L:=L) f*size (L:=L) g :=
    le_of_sq_le_sq cs (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have ex (s : ℝ) : ((f+g) s)^2=f s^2+g s^2+2*(f s*g s) := by simp only [Pi.add_apply]; ring
  have id : mass (L:=L) (f+g)=mass (L:=L) f+mass (L:=L) g+2*I := by
    unfold mass
    simp_rw [ex]
    rw [intervalIntegral.integral_add (f:=fun s => f s^2+g s^2) (g:=fun s=>2*(f s*g s))
      (((cf.pow 2).add (cg.pow 2)).intervalIntegrable ..) (((cf.mul cg).const_mul 2).intervalIntegrable ..),
      intervalIntegral.integral_add (f:=fun s=>f s^2) (g:=fun s=>g s^2) ((cf.pow 2).intervalIntegrable ..)
        ((cg.pow 2).intervalIntegrable ..),intervalIntegral.integral_const_mul]
  apply le_of_sq_le_sq _ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  change size (L:=L) (f+g)^2 ≤ (size (L:=L) f+size (L:=L) g)^2
  nlinarith only [size_sq lp (f+g),id,size_sq lp f,size_sq lp g,cross]

theorem size_change {f g : ℝ→ℝ} {r : ℝ} (lp : 0≤L) (rp : 0≤r) (cf : Continuous f) (cg : Continuous g)
    (pt : ∀s∈Icc 0 L,(f s-g s)^2≤r^2) :
    size (L:=L) f≤size (L:=L) g+r*Real.sqrt L := by
  have bd : mass (L:=L) (f-g)≤L*r^2 := by
    have h := intervalIntegral.integral_mono_on lp (((cf.sub cg).pow 2).intervalIntegrable (μ:=volume) 0 L)
      (g:=fun (_:ℝ) => r^2) (continuous_const.intervalIntegrable ..) pt
    simpa only [mass,Pi.pow_apply,intervalIntegral.integral_const,sub_zero,smul_eq_mul] using h
  have diff : size (L:=L) (f-g)≤r*Real.sqrt L := by
    apply le_of_sq_le_sq _ (mul_nonneg rp (Real.sqrt_nonneg _))
    rw [size_sq lp,mul_pow,Real.sq_sqrt lp,mul_comm]; exact bd
  have tri := size_triangle (f:=g) (g:=f-g) lp cg (cf.sub cg)
  rw [show g+(f-g)=f by abel] at tri
  linarith only [tri,diff]

private theorem cs2 (a b x y : ℝ) :
    (a*x+b*y)^2≤(a^2+b^2)*(x^2+y^2) := by nlinarith only [sq_nonneg (a*y-b*x)]

theorem moved_support_bounds {r : ℝ} {d : Fin 2 → ℝ} (lp : 0≤L) (rp : 0≤r)
    (ball : d 0^2+d 1^2≤r^2) :
    size (L:=L) (c.p 0)≤size (L:=L) (c.p d)+r*Real.sqrt L ∧
    size (L:=L) (c.q d)≤size (L:=L) (c.q 0)+r*Real.sqrt L := by
  constructor
  · apply size_change lp rp (c.contP 0) (c.contP d)
    intro s _
    have cs := cs2 (d 0) (d 1) (-deriv c.y s) (deriv c.x s)
    rw [neg_sq,add_comm ((deriv c.y s)^2),c.unit s,mul_one] at cs
    change ((-((c.x s)-0)*deriv c.y s+(c.y s-0)*deriv c.x s)-
      (-((c.x s)-d 0)*deriv c.y s+(c.y s-d 1)*deriv c.x s))^2≤_
    nlinarith only [cs,ball]
  · apply size_change lp rp (c.contQ d) (c.contQ 0)
    intro s _
    have cs := cs2 (d 0) (d 1) (deriv c.x s) (deriv c.y s)
    rw [c.unit s,mul_one] at cs
    change ((c.x s-d 0)*deriv c.x s+(c.y s-d 1)*deriv c.y s-
      ((c.x s-0)*deriv c.x s+(c.y s-0)*deriv c.y s))^2≤_
    nlinarith only [cs,ball]

theorem moved_radius_bound {r R : ℝ} {d : Fin 2 → ℝ} (rp : 0≤r) (Rp : 0≤R)
    (ball : d 0^2+d 1^2≤r^2) (cap : ∀s∈Icc 0 L,c.radialSq 0 s≤R^2) :
    ∀s∈Icc 0 L,c.radialSq d s≤(R+r)^2 := by
  intro s hs
  have xy := cap s hs
  simp only [radialSq,Pi.zero_apply,sub_zero] at xy
  have cs := cs2 (d 0) (d 1) (c.x s) (c.y s)
  have mm := mul_le_mul ball xy (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg r)
  have low : -(d 0*c.x s+d 1*c.y s) ≤ r*R := by
    apply le_of_sq_le_sq _ (mul_nonneg rp Rp)
    rw [neg_sq,mul_pow]
    exact cs.trans mm
  dsimp only [radialSq]
  nlinarith only [low,xy,ball]

end MigrationGeometry.Rotating.UnitLoop
#print axioms MigrationGeometry.Rotating.UnitLoop.moved_support_bounds
#print axioms MigrationGeometry.Rotating.UnitLoop.moved_radius_bound
