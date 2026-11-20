import Migration.AdjointHalfspace
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-! Actual pure homothetic expanders whose centered radius obeys
rate times R^4 ≤ 2 have image points on both sides of every line through
the expansion center. The center is the origin in these coordinates. -/
noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Adjoint

structure ClosedExpander (rate L : ℝ) where
  x : ℝ → ℝ
  y : ℝ → ℝ
  hx : ContDiff ℝ ∞ x
  hy : ContDiff ℝ ∞ y
  px : Function.Periodic x L
  py : Function.Periodic y L
  unit (s : ℝ) : (deriv x s)^2+(deriv y s)^2=1
  profile (s : ℝ) : elasticForce x y s= -rate*normalSupport x y 0 s

namespace ClosedExpander
variable {rate L : ℝ} (c : ClosedExpander rate L)

def projected (a b : ℝ) : Frame rate L := by
  let X := deriv c.x
  let Y := deriv c.y
  let k := signedCurvature c.x c.y
  have hx (s : ℝ) := (c.hx.differentiable (by simp) s).hasDerivAt
  have hy (s : ℝ) := (c.hy.differentiable (by simp) s).hasDerivAt
  have hX (s : ℝ) : HasDerivAt X (-k s*Y s) s :=
    (((contDiff_infty_iff_deriv.mp c.hx).2.differentiable (by simp) s).hasDerivAt).congr_deriv
      (frenet_x c.hx c.hy c.unit s)
  have hY (s : ℝ) : HasDerivAt Y (k s*X s) s :=
    (((contDiff_infty_iff_deriv.mp c.hy).2.differentiable (by simp) s).hasDerivAt).congr_deriv
      (frenet_y c.hx c.hy c.unit s)
  have hk := signedCurvature_smooth c.hx c.hy
  let v := deriv k
  refine {
    k := k, v := v, p := fun s => -c.x s*Y s+c.y s*X s,
    q := fun s => c.x s*X s+c.y s*Y s,
    h := fun s => a*c.x s+b*c.y s, u := fun s => a*X s+b*Y s,
    n := fun s => -a*Y s+b*X s,
    kD := fun s => (hk.differentiable (by simp) s).hasDerivAt,
    vD := ?_, pD := ?_, qD := ?_, hD := fun s => ((hx s).const_mul a).add ((hy s).const_mul b),
    uD := ?_, nD := ?_, decompose := ?_, periodic := ?_ }
  · intro s
    apply ((contDiff_infty_iff_deriv.mp hk).2.differentiable (by simp) s).hasDerivAt.congr_deriv
    have h := c.profile s
    simp only [elasticForce,normalSupport,Pi.zero_apply,sub_zero] at h
    dsimp [k,X,Y]
    linarith
  · intro s
    apply (((hx s).neg.mul (hY s)).add ((hy s).mul (hX s))).congr_deriv
    dsimp [X,Y]
    ring
  · intro s
    apply (((hx s).mul (hX s)).add ((hy s).mul (hY s))).congr_deriv
    dsimp [X,Y]
    linear_combination c.unit s
  · intro s
    apply (((hX s).const_mul a).add ((hY s).const_mul b)).congr_deriv
    ring
  · intro s
    apply (((hY s).const_mul (-a)).add ((hX s).const_mul b)).congr_deriv
    ring
  · intro s
    dsimp [X,Y]
    linear_combination -(a*c.x s+b*c.y s)*c.unit s
  · intro s
    dsimp only [k,v,X,Y]
    simp only [signedCurvature_periodic c.px c.py s,
      periodic_actual_deriv (signedCurvature_periodic c.px c.py) s,
      c.px s,c.py s,periodic_actual_deriv c.px s,periodic_actual_deriv c.py s,and_self]

private theorem has_negative_height {R : ℝ} (hr : 0<rate) (hL : 0<L) (hcap : rate*R^4≤2)
    (hb : ∀ s, (c.x s)^2+(c.y s)^2≤R^2) {a b : ℝ} (he : 0<a^2+b^2) :
    ∃ s ∈ Icc 0 L, a*c.x s+b*c.y s<0 := by
  let f := c.projected a b
  have hframe (s : ℝ) : (f.p s)^2+(f.q s)^2=(c.x s)^2+(c.y s)^2 := by
    change (-c.x s*deriv c.y s+c.y s*deriv c.x s)^2+
        (c.x s*deriv c.x s+c.y s*deriv c.y s)^2=_
    linear_combination ((c.x s)^2+(c.y s)^2)*c.unit s
  by_contra! hn
  have hp : Function.Periodic f.h L := fun s => (f.periodic s).2.2.2.2.1
  have hnon (s) : 0≤f.h s := by
    obtain ⟨t,ht,heq⟩ := hp.exists_mem_Ico₀ hL s
    rw [heq]
    exact hn t ⟨ht.1,ht.2.le⟩
  have hz := f.height_zero_of_nonneg hr hL hcap (fun s => (hframe s).le.trans (hb s)) hnon
  have hu (s : ℝ) : f.u s=0 := (f.hD s).unique
    ((hasDerivAt_const s (0:ℝ)).congr_of_eventuallyEq (Filter.Eventually.of_forall hz))
  let g := fun s => -b*c.x s+a*c.y s
  have hg : Continuous g := (c.hx.continuous.const_mul (-b)).add (c.hy.continuous.const_mul a)
  have hgd (s : ℝ) : HasDerivAt g (-f.n s) s := by
    apply ((((c.hx.differentiable (by simp) s).hasDerivAt.const_mul (-b)).add
      ((c.hy.differentiable (by simp) s).hasDerivAt.const_mul a))).congr_deriv
    change _ = -(-a*deriv c.y s+b*deriv c.x s)
    ring
  have rend : g 0=g L := by
    have hx := c.px 0
    have hy := c.py 0
    rw [zero_add] at hx hy
    simp only [g,hx,hy]
  obtain ⟨s,_,hs⟩ := exists_hasDerivAt_eq_zero hL hg.continuousOn rend (fun s _ => hgd s)
  have h1 := hu s
  change a*deriv c.x s+b*deriv c.y s=0 at h1
  change -(-a*deriv c.y s+b*deriv c.x s)=0 at hs
  have normId : (a*deriv c.x s+b*deriv c.y s)^2+(-(-a*deriv c.y s+b*deriv c.x s))^2 =
      a^2+b^2 := by linear_combination (a^2+b^2)*c.unit s
  rw [h1,hs] at normId
  linarith

/-- Directional form of interior convex-hull containment of the expansion
center. Both witnesses belong to the image over one actual arclength period. -/
theorem both_sides_of_every_center_line {R : ℝ} (hr : 0<rate) (hL : 0<L) (hcap : rate*R^4≤2)
    (hb : ∀ s, (c.x s)^2+(c.y s)^2≤R^2) {a b : ℝ} (he : 0<a^2+b^2) :
    (∃ s ∈ Icc 0 L, a*c.x s+b*c.y s<0) ∧ (∃ s ∈ Icc 0 L, 0<a*c.x s+b*c.y s) := by
  refine ⟨c.has_negative_height hr hL hcap hb he,?_⟩
  obtain ⟨t,ht,h⟩ := c.has_negative_height hr hL hcap hb (a := -a) (b := -b) (by simpa using he)
  exact ⟨t,ht,by linarith⟩

/-- Images of two positive homothetic copies with a common translated center
cannot lie in opposite strict half-planes of the same fixed line. -/
theorem no_homothetic_halfplane_migration {R : ℝ} (hr : 0<rate) (hL : 0<L) (hcap : rate*R^4≤2)
    (hb : ∀ s, (c.x s)^2+(c.y s)^2≤R^2) {a b : ℝ} (he : 0<a^2+b^2)
    {r₀ r₁ : ℝ} (hr₀ : 0<r₀) (hr₁ : 0<r₁) (center line : ℝ) :
    ¬ ((∀ s ∈ Icc 0 L, line<center+r₀*(a*c.x s+b*c.y s)) ∧
       (∀ s ∈ Icc 0 L, center+r₁*(a*c.x s+b*c.y s)<line)) := by
  intro ⟨hzero,hone⟩
  obtain ⟨⟨s,hs,hneg⟩,⟨t,ht,hpos⟩⟩ := c.both_sides_of_every_center_line hr hL hcap hb he
  linarith only [hzero s hs,hone t ht,mul_neg_of_pos_of_neg hr₀ hneg,mul_pos hr₁ hpos]

end ClosedExpander
end MigrationGeometry.Adjoint
