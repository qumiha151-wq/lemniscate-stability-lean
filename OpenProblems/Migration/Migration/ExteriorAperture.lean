import Migration.SeparatedHeight
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace MigrationGeometry.Adjoint

private theorem pointwise_defect {r p q h u n z : ℝ} (rp : 0<r) (zp : 0≤z)
    (rad : p^2+q^2=r^2) (unit : u^2+n^2=1) (frame : h=q*u+p*n) (cone : z*r≤h) :
    p^2/r ≤ (1-z^2)*r+2*z*(p*n) ∧
      (n≠0 → 0<z → p^2/r < (1-z^2)*r+2*z*(p*n)) := by
  have exactDefect : ((1-z^2)*r+2*z*(p*n))*r-p^2 =
      (z*r*n)^2+(q-z*r*u)^2+2*z*r*(h-z*r) := by
    rw [frame]
    linear_combination -rad-z^2*r^2*unit
  have coneSign := mul_nonneg (show 0≤2*z*r by positivity) (sub_nonneg.mpr cone)
  constructor
  · apply (div_le_iff₀ rp).mpr
    linarith only [exactDefect,sq_nonneg (z*r*n),sq_nonneg (q-z*r*u),coneSign]
  · intro nn zz
    apply (div_lt_iff₀ rp).mpr
    linarith only [exactDefect,sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero zz.ne' rp.ne') nn),
      sq_nonneg (q-z*r*u),coneSign]

namespace Frame
variable {rate L : ℝ} (f : Frame rate L)

private theorem projected_balance (hr : 0<rate) :
    (∫ s in 0..L, f.p s*f.n s)=0 := by
  have cp := continuous_iff_continuousAt.mpr fun s => (f.pD s).continuousAt
  have cn := continuous_iff_continuousAt.mpr fun s => (f.nD s).continuousAt
  have d (s : ℝ) : HasDerivAt f.stress ((-rate)*(f.p s*f.n s)) s := by
    convert! f.stressD s using 1
    ring
  have val := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=L)
    (fun s _ => d s) (((cp.mul cn).const_mul (-rate)).intervalIntegrable 0 L)
  obtain ⟨k,v,_,_,_,u,n⟩ := f.periodic 0
  simp only [zero_add] at k v u n
  rw [intervalIntegral.integral_const_mul,show f.stress L=f.stress 0 by simp [stress,k,v,u,n],
    sub_self] at val
  exact (mul_eq_zero.mp val).resolve_left (neg_ne_zero.mpr hr.ne')

/-- The positive normal projection at a critical point of the periodic
    height makes the integrated sector inequality strict. -/
theorem sector_integral {r : ℝ → ℝ} {z : ℝ} (hr : 0<rate) (hL : 0<L)
    (hz : 0<z) (cr : Continuous r) (rp : ∀ s, 0<r s)
    (rad : ∀ s, f.p s^2+f.q s^2=r s^2) (unit : ∀ s, f.u s^2+f.n s^2=1)
    (cone : ∀ s∈Icc 0 L, z*r s ≤ f.h s) :
    (∫ s in 0..L, f.p s^2/r s) < (1-z^2)*(∫ s in 0..L, r s) := by
  have cp := continuous_iff_continuousAt.mpr fun s => (f.pD s).continuousAt
  have cn := continuous_iff_continuousAt.mpr fun s => (f.nD s).continuousAt
  have ch := continuous_iff_continuousAt.mpr fun s => (f.hD s).continuousAt
  have ends : f.h 0=f.h L := by simpa using (f.periodic 0).2.2.2.2.1.symm
  obtain ⟨t,ht,hu⟩ := exists_hasDerivAt_eq_zero hL ch.continuousOn ends
    (fun s _ => f.hD s)
  have nn : f.n t ≠ 0 := by intro h; have a := unit t; rw [hu,h] at a; norm_num at a
  have defc s (hs : s∈Icc 0 L) := pointwise_defect (rp s) hz.le (rad s)
    (unit s) (f.decompose s) (cone s hs)
  have val := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hL
    (((cp.pow 2).div cr (fun s => (rp s).ne')).continuousOn)
    (((cr.const_mul (1-z^2)).add ((cp.mul cn).const_mul (2*z))).continuousOn)
    (fun s hs => (defc s ⟨hs.1.le,hs.2⟩).1) ⟨t,⟨ht.1.le,ht.2.le⟩,(defc t ⟨ht.1.le,ht.2.le⟩).2 nn hz⟩
  change (∫ s in 0..L, f.p s^2/r s) < ∫ s in 0..L, (1-z^2)*r s+2*z*(f.p s*f.n s) at val
  rw [intervalIntegral.integral_add (f:=fun s => (1-z^2)*r s) (g:=fun s => 2*z*(f.p s*f.n s))
    ((cr.const_mul (1-z^2)).intervalIntegrable 0 L)
    (((cp.mul cn).const_mul (2*z)).intervalIntegrable 0 L),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    f.projected_balance hr,mul_zero,add_zero] at val
  exact val
end Frame

namespace ClosedExpander
variable {rate L : ℝ} (c : ClosedExpander rate L)

def centeredRadius (s : ℝ) : ℝ := Real.sqrt (c.x s^2+c.y s^2)

private theorem support_mass :
    (∫ s in 0..L, signedCurvature c.x c.y s^2) =
      2*rate*(∫ s in 0..L, normalSupport c.x c.y 0 s^2) := by
  have vir := elasticForce_normalSupport_integral c.hx c.hy c.px c.py c.unit 0
  have val : (∫ s in 0..L, elasticForce c.x c.y s * normalSupport c.x c.y 0 s) =
      -rate*(∫ s in 0..L, normalSupport c.x c.y 0 s^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    change elasticForce c.x c.y s * normalSupport c.x c.y 0 s = _
    rw [c.profile]; ring
  rw [val] at vir
  dsimp [bendingEnergy] at vir
  linarith

/-- For an arbitrary positive dilation rate, the actual radius and the
    cosine of any enclosing sector's half-angle obey this strict bound. -/
theorem radius_sector_bound {a b z R : ℝ} (hr : 0<rate) (hL : 0<L)
    (direction : a^2+b^2=1) (hz : 0<z) (hz1 : z≤1)
    (rp : ∀ s, 0<c.centeredRadius s) (radius : ∀ s∈Icc 0 L, c.centeredRadius s≤R)
    (cone : ∀ s∈Icc 0 L, z*c.centeredRadius s≤a*c.x s+b*c.y s) :
    1 < 2*rate*((1-z^2)*R^2)^2 := by
  let f := c.projected a b
  let r := c.centeredRadius
  have cr : Continuous r := ((c.hx.continuous.pow 2).add (c.hy.continuous.pow 2)).sqrt
  have rad (s) : f.p s^2+f.q s^2=r s^2 := by
    rw [show r s^2=c.x s^2+c.y s^2 from Real.sq_sqrt (by positivity)]
    change (-c.x s*deriv c.y s+c.y s*deriv c.x s)^2+
      (c.x s*deriv c.x s+c.y s*deriv c.y s)^2=_
    linear_combination (c.x s^2+c.y s^2)*c.unit s
  have unit (s) : f.u s^2+f.n s^2=1 := by
    change (a*deriv c.x s+b*deriv c.y s)^2+(-a*deriv c.y s+b*deriv c.x s)^2=1
    linear_combination (a^2+b^2)*c.unit s+direction
  have en := f.sector_integral hr hL hz cr rp rad unit cone
  let P := ∫ s in 0..L, f.p s^2
  have hR := (rp 0).trans_le (radius 0 ⟨le_rfl,hL.le⟩)
  have posZ : 0≤1-z^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hz1) (show 0≤1+z by positivity)]
  have cp := continuous_iff_continuousAt.mpr fun s => (f.pD s).continuousAt
  have low : P ≤ R*(∫ s in 0..L, f.p s^2/r s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hL.le ((cp.pow 2).intervalIntegrable 0 L)
      ((((cp.pow 2).div cr (fun s => (rp s).ne')).const_mul R).intervalIntegrable 0 L)
    intro s hs
    change f.p s^2 ≤ R*(f.p s^2/r s)
    rw [← mul_div_assoc,le_div_iff₀ (rp s)]
    exact (mul_le_mul_of_nonneg_left (radius s hs) (sq_nonneg _)).trans_eq (mul_comm ..)
  have high := intervalIntegral.integral_mono_on (μ:=volume) hL.le (cr.intervalIntegrable 0 L)
    (continuous_const.intervalIntegrable 0 L) radius
  change (∫ s in 0..L, r s) ≤ ∫ _ in (0:ℝ)..L, R at high
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at high
  have bound : P < L*((1-z^2)*R^2) := by
    have a := low.trans_lt (mul_lt_mul_of_pos_left en hR)
    have b := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left high posZ) hR.le
    nlinarith only [a,b]
  have mass : (∫ s in 0..L, signedCurvature c.x c.y s^2)=2*rate*P := by
    simpa only [P,f,projected,normalSupport,Pi.zero_apply,sub_zero] using c.support_mass
  have cs := MigrationGeometry.Flow.interval_integral_mul_sq_le
    (signedCurvature_smooth c.hx c.hy).continuous (normalSupport_continuous c.hx c.hy 0) hL.le
  rw [curvature_normalSupport_integral c.hx c.hy c.px c.py c.unit 0,mass] at cs
  change (-L)^2≤(2*rate*P)*(∫ s in 0..L, normalSupport c.x c.y 0 s^2) at cs
  have pEq : (∫ s in 0..L, normalSupport c.x c.y 0 s^2)=P := by
    simp only [P,f,projected,normalSupport,Pi.zero_apply,sub_zero]
  rw [pEq] at cs
  have gp : 0≤P := intervalIntegral.integral_nonneg hL.le (fun s _ => sq_nonneg _)
  have bs := mul_lt_mul_of_pos_left (pow_lt_pow_left₀ bound gp (show 2≠0 by decide))
    (show 0<2*rate by positivity)
  by_contra! bad
  nlinarith only [cs,bs,mul_le_mul_of_nonneg_right bad (sq_nonneg L)]

end ClosedExpander
end MigrationGeometry.Adjoint
#print axioms MigrationGeometry.Adjoint.Frame.sector_integral
#print axioms MigrationGeometry.Adjoint.ClosedExpander.radius_sector_bound
