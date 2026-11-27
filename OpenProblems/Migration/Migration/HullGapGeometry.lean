import Migration.ExpanderCenterHull
import Migration.HullFrameScaling
import Migration.EscapingHulls

noncomputable section
open Set
namespace MigrationGeometry.HullGap
open Adjoint

/-- Uniform centred disk containment for actual profiles of any positive rate,
    with a radius threshold strictly larger than the pointwise bound two. -/
theorem expander_hull_disk_of_margin
    (normalized : ∃ ε>0, ∀ (L : ℝ), 0<L → ∀ (f : Frame 1 L),
    (∀ s, ((f.p s)^2+(f.q s)^2)^2≤2+ε) →
    (∀ s, (f.u s)^2+(f.n s)^2=1) → ∃ s∈Icc 0 L, f.h s < -ε) : ∃ δ>0, ∃ η>0, ∀ (a L : ℝ), 0<a → 0<L →
    ∀ (c : ClosedExpander (a^4) L), (∀ s, a^4*((c.x s)^2+(c.y s)^2)^2≤2+δ) →
    Metric.closedBall (0:ℂ) (η/a) ⊆ convexHull ℝ ((fun s => (c.x s:ℂ)+(c.y s:ℂ)*Complex.I) '' Icc 0 L) := by
  obtain ⟨d,dp,margin⟩ := normalized
  refine ⟨d,dp,d/2,by positivity,fun a L ap Lp c rad => ?_⟩
  apply Flow.closedBall_subset_convexHull_of_directional_margin (r:=d/2/a) (R:=d/a) ((div_lt_div_iff_of_pos_right ap).mpr (by linarith))
  intro e he
  let f := c.projected (-e.re) (-e.im)
  have norm : e.re^2+e.im^2=1 := by
    have h := e.sq_norm
    rw [he,Complex.normSq_apply] at h
    nlinarith only [h]
  have r (s : ℝ) : (f.p s)^2+(f.q s)^2=(c.x s)^2+(c.y s)^2 := by
    change (-c.x s*deriv c.y s+c.y s*deriv c.x s)^2+
      (c.x s*deriv c.x s+c.y s*deriv c.y s)^2=_
    linear_combination (c.x s^2+c.y s^2)*c.unit s
  have un (s : ℝ) : (f.u s)^2+(f.n s)^2=1 := by
    change (-e.re*deriv c.x s+ -e.im*deriv c.y s)^2+(- -e.re*deriv c.y s+ -e.im*deriv c.x s)^2=1
    linear_combination (e.re^2+e.im^2)*c.unit s+norm
  let F := f.normalize ap rfl
  have rr (s : ℝ) : ((F.p s)^2+(F.q s)^2)^2≤2+d := by
    change ((a*f.p (s/a))^2+(a*f.q (s/a))^2)^2≤2+d
    calc
      _ = a^4*((f.p (s/a))^2+(f.q (s/a))^2)^2 := by ring
      _ ≤ _ := by rw [r]; exact rad _
  obtain ⟨t,ht,h⟩ := margin (a*L) (mul_pos ap Lp) F rr (fun s => un (s/a))
  let s := t/a
  have hs : s∈Icc 0 L := ⟨div_nonneg ht.1 ap.le,(div_le_iff₀ ap).mpr (by linarith [ht.2])⟩
  have hit : d/a < e.re*c.x s+e.im*c.y s := by
    apply (div_lt_iff₀ ap).mpr
    change a*(-e.re*c.x s+ -e.im*c.y s)< -d at h
    linarith only [h]
  refine ⟨_,⟨s,hs,rfl⟩,?_⟩
  simp only [inner_zero_right,zero_add,Complex.inner,Complex.add_re,Complex.mul_re,
    Complex.conj_re,Complex.conj_im,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,zero_add]
  linarith

end MigrationGeometry.HullGap
#print axioms MigrationGeometry.HullGap.expander_hull_disk_of_margin
