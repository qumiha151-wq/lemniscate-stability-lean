import Migration.ForceLobeJet
import Migration.RotatingHullDisk

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Rotating.UnitLoop
variable {L : ℝ} (c : UnitLoop L)

/-- Opposite normals can supply a positive or negative force witness,
and the witnesses may belong to different parts of the curve. -/
def signedNormalCover (f : ℝ) : Prop := ∀ U V : ℝ, U^2+V^2=1 →
    (∃s, -deriv c.y s=U ∧ deriv c.x s=V ∧ f≤c.F s) ∨
    (∃s, -deriv c.y s= -U ∧ deriv c.x s= -V ∧ c.F s≤ -f)

theorem negative_height_witness {a b A B f : ℝ} (sol : c.IsRotating a b)
    (unit : A^2+B^2=1) (cover : c.signedNormalCover f) :
    ∃s, a*Real.sqrt (1+b^2)*(A*c.x s+B*c.y s) ≤ -f := by
  let d := Real.sqrt (1+b^2)
  have dp : 0<d := Real.sqrt_pos.mpr (by positivity)
  have ds : d^2=1+b^2 := Real.sq_sqrt (by positivity)
  let U := (A-b*B)/d
  let V := (B+b*A)/d
  have uv : U^2+V^2=1 := by
    dsimp only [U,V]
    field_simp
    linear_combination (1+b^2)*unit-ds
  have x : U+b*V=d*A := by
    dsimp only [U,V]; field_simp; linear_combination -A*ds
  have y : V-b*U=d*B := by
    dsimp only [U,V]; field_simp; linear_combination -B*ds
  rcases cover U V uv with ⟨s,hs,ht,positive⟩ | ⟨s,hs,ht,negative⟩
  · have eq := c.force_normal_height sol hs ht
    rw [x,y] at eq
    exact ⟨s,by change a*d*(A*c.x s+B*c.y s)≤ -f; linarith only [eq,positive]⟩
  · have eq := c.force_normal_height sol hs ht
    rw [show -U+b*(-V)= -(U+b*V) by ring,show -V-b*(-U)= -(V-b*U) by ring,x,y] at eq
    exact ⟨s,by change a*d*(A*c.x s+B*c.y s)≤ -f; linarith only [eq,negative]⟩

/-- All separated similarity times are excluded by the signed normal cover,
with an explicit centered disk if the actual force witnesses are strict. -/
theorem centered_disk_of_signed_force_cover {a b f r : ℝ} (ap : 0<a) (lp : 0<L)
    (sol : c.IsRotating a b) (cover : c.signedNormalCover f)
    (margin : a*Real.sqrt (1+b^2)*r≤f) :
    Metric.closedBall (0:ℂ) r ⊆ convexHull ℝ c.traceSet := by
  intro z hz
  by_contra out
  obtain ⟨A,B,unit,sep⟩ := c.exterior_separator lp out
  obtain ⟨s,hs⟩ := c.negative_height_witness sol unit cover
  have dpos : 0<a*Real.sqrt (1+b^2) := mul_pos ap (Real.sqrt_pos.mpr (by positivity))
  have small : A*c.x s+B*c.y s≤ -r := by
    apply le_of_mul_le_mul_left (a:=a*Real.sqrt (1+b^2)) (by linarith only [hs,margin]) dpos
  have nz : ‖z‖≤r := by simpa [Metric.mem_closedBall,dist_zero_right] using hz
  have en : ‖((A:ℂ)+(B:ℂ)*Complex.I)‖=1 := by
    rw [Complex.norm_def]; simp [Complex.normSq_apply]; nlinarith only [unit]
  have cs := real_inner_le_norm (-((A:ℂ)+(B:ℂ)*Complex.I)) z
  rw [norm_neg,en,one_mul,inner_neg_left,Complex.inner] at cs
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,mul_zero,
    mul_one,zero_add,add_zero,sub_zero] at cs
  have h := sep s
  change 0<A*(c.x s-z.re)+B*(c.y s-z.im) at h
  linarith only [small,h,cs,nz]

end MigrationGeometry.Rotating.UnitLoop

#print axioms MigrationGeometry.Rotating.UnitLoop.centered_disk_of_signed_force_cover
