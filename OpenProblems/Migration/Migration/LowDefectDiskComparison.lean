import Migration.LowDefectVirial
import Migration.LowDefectModes

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem support_moment_root {J L : ℝ} (j : 0 ≤ J) (l : 0 ≤ L)
    (w : (2*Real.pi)^2*J ≤ L^3) :
    (2*Real.pi)*Real.sqrt J ≤ L*Real.sqrt L := by
  have lhs : ((2*Real.pi)*Real.sqrt J)^2 = (2*Real.pi)^2*J := by
    rw [mul_pow,Real.sq_sqrt j]
  have rhs : (L*Real.sqrt L)^2 = L^3 := by rw [mul_pow,Real.sq_sqrt l]; ring
  nlinarith only [lhs,rhs,w,show 0 ≤ L*Real.sqrt L by positivity]

/-- Given the two static one-slice tangent Fourier estimates on the
physical time slab, the full flow supplies the dissipation, virial,
centroid drift and the common disk with the stated numerical radius. -/
theorem physical_disk_of_fourier_estimates (hf : c.IsNormalFEF)
    {s t : ℝ} (hst : s ≤ t) (slab : Icc s t ⊆ I)
    (x : ℝ → ℝ) (nonneg : ∀v ∈ Icc s t, 0 ≤ x v)
    (small : ∀v ∈ Icc s t, x v ≤ 374/1000)
    (prod : ∀v ∈ Icc s t, c.bending v*c.coreLength v =
      2*Real.pi^2*(1+(x v)^2))
    (flux : ∀e : ℂ, ‖e‖=1 → ∀v ∈ Icc s t,
      Real.sqrt (c.centroidFluxMoment (innerSL ℝ e) v) ≤
        x v*(1750/1000+575/1000*x v+133/1000*(x v)^2)*Real.sqrt (c.coreLength v))
    (support : ∀e : ℂ, ‖e‖=1 → ∃u ∈ Icc 0 c.period,
      inner ℝ e (c.arclengthCentroid t) +
        c.coreLength t/(2*Real.pi)*(1-575/1000*x t-265/1000*(x t)^2) ≤
      inner ℝ e (c.position t u)) :
    Metric.closedBall (c.arclengthCentroid s)
      ((846/1000)*Real.pi/c.bending s+(4/1000)*Real.pi/c.bending t) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  have pos (v) (hv : v ∈ Icc s t) : 0 < c.bending v := by
    have hh : 0 < 2*Real.pi^2*(1+(x v)^2) := by positivity
    exact pos_of_mul_pos_left ((prod v hv).symm ▸ hh) (c.coreLength_pos (slab hv)).le
  have ht : t ∈ Icc s t := ⟨hst,le_rfl⟩
  have pp : 0 < 2*Real.pi := by positivity
  apply c.earlier_ball_of_spatial_flux_moments hf hst slab pos
      (α:=(846/1000)*Real.pi) (β:=(852/1000)*Real.pi)
  · intro e he v hv
    let L := c.coreLength v
    let E := c.bending v
    let H := innerSL ℝ e
    let M := c.centroidFluxMoment H v
    let J := c.centeredSupportMoment v
    let q := x v*(1750/1000+575/1000*x v+133/1000*(x v)^2)
    have lpos : 0 < L := c.coreLength_pos (slab hv)
    have jpos : 0 ≤ J := intervalIntegral.integral_nonneg_of_forall c.period_pos.le
      (fun u=>mul_nonneg (sq_nonneg _) (speed_pos (c.immersion v (slab hv)) u).le)
    have jm := support_moment_root jpos lpos.le (c.centered_support_wirtinger (slab hv))
    have qb : 0 ≤ q := by dsimp [q]; positivity [nonneg v hv]
    have mb : Real.sqrt M ≤ q*Real.sqrt L := flux e he v hv
    have both := mul_le_mul mb jm (by positivity) (mul_nonneg qb (Real.sqrt_nonneg L))
    have de : q*Real.sqrt L*(L*Real.sqrt L)=q*L^2 := by
      calc _ = q*L*(Real.sqrt L)^2 := by ring
           _ = _ := by rw [Real.sq_sqrt lpos.le]; ring
    rw [de] at both
    have be := mul_le_mul_of_nonneg_left both (pos v hv).le
    have md : (1+(x v)^2)*q ≤ 846/1000 := by
      simpa only [q,mul_assoc] using (LowDefect.physical_margins (nonneg v hv) (small v hv)).1.le
    have m2 := mul_le_mul_of_nonneg_right md (show 0 ≤ 2*Real.pi^2*L by positivity)
    have ep : E*L=2*Real.pi^2*(1+(x v)^2) := prod v hv
    have eb : E*(q*L^2)=((1+(x v)^2)*q)*(2*Real.pi^2*L) := by
      calc _ = (E*L)*(q*L) := by ring
           _ = _ := by rw [ep]; ring
    change E*Real.sqrt M*Real.sqrt J ≤ (846/1000)*Real.pi*L
    apply (mul_le_mul_iff_left₀ pp).mp
    change E*(Real.sqrt M*(2*Real.pi*Real.sqrt J)) ≤ _ at be
    rw [show (E*Real.sqrt M*Real.sqrt J)*(2*Real.pi)=
      E*(Real.sqrt M*(2*Real.pi*Real.sqrt J)) by ring]
    calc _ ≤ E*(q*L^2) := be
         _ = _ := eb
         _ ≤ _ := by linarith only [m2, show (846/1000:ℝ)*(2*Real.pi^2*L)=
                        ((846/1000)*Real.pi*L)*(2*Real.pi) by ring]
  · intro e he
    obtain ⟨u,hu,sup⟩ := support e he
    refine ⟨u,hu,?_⟩
    apply le_trans _ sup
    apply add_le_add_right
    apply (div_le_iff₀ (pos t ht)).mpr
    have hprod := prod t ht
    have marg := (LowDefect.physical_margins (nonneg t ht) (small t ht)).2.le
    apply (mul_le_mul_iff_left₀ pp).mp
    have h := mul_le_mul_of_nonneg_right marg (show 0 ≤ 2*Real.pi^2 by positivity)
    have de : c.coreLength t/(2*Real.pi)*(1-575/1000*x t-265/1000*(x t)^2) *
        c.bending t*(2*Real.pi) =
        (1+(x t)^2)*(1-575/1000*x t-265/1000*(x t)^2)*(2*Real.pi^2) := by
      rw [show (1+(x t)^2)*(1-575/1000*x t-265/1000*(x t)^2)*(2*Real.pi^2)=
        (2*Real.pi^2*(1+(x t)^2))*(1-575/1000*x t-265/1000*(x t)^2) by ring,←hprod]
      field_simp [Real.pi_ne_zero]
    rw [de]
    linarith only [h,show (852/1000:ℝ)*Real.pi*(2*Real.pi)=(852/1000)*(2*Real.pi^2) by ring]
  · have h : (4/1000:ℝ)*Real.pi < (852/1000)*Real.pi-(846/1000)*Real.pi := by
      linarith [Real.pi_pos]
    exact add_lt_add_right ((div_lt_div_iff_of_pos_right (pos t ht)).mpr h) _

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.physical_disk_of_fourier_estimates
