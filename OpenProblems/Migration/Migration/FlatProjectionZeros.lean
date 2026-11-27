import Migration.SingularEndpointAction
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set
namespace MigrationGeometry.AngularExcursion

/-- Arbitrarily close distinct labels at which a scalar projection vanishes. -/
def accumulatingZeros (f : ℝ→ℝ) (a : ℝ) : Prop :=
  ∀r>0,∃b : ℝ,b≠a ∧ |b-a|<r ∧ f b=0

theorem value_at_accumulating_zeros {f : ℝ→ℝ} {a : ℝ} (cf : ContinuousAt f a)
    (zero : accumulatingZeros f a) : f a=0 := by
  by_contra nonzero
  obtain ⟨d,dp,bd⟩ := Metric.continuousAt_iff.mp cf _ (abs_pos.mpr nonzero)
  obtain ⟨b,_,close,fb⟩ := zero d dp
  have h := bd (show dist b a<d from close)
  rw [Real.dist_eq,fb,zero_sub,abs_neg] at h
  exact (lt_irrefl _) h

theorem rolle_at_accumulating_zeros {f d : ℝ→ℝ} {a : ℝ} (df : ∀s,HasDerivAt f (d s) s)
    (zero : accumulatingZeros f a) : accumulatingZeros d a := by
  have cf := continuous_iff_continuousAt.mpr (fun r=>(df r).continuousAt)
  have fa := value_at_accumulating_zeros cf.continuousAt zero
  intro r rp
  obtain ⟨b,ne,bd,fb⟩ := zero r rp
  rcases lt_or_gt_of_ne ne with l|l
  · obtain ⟨x,hx,dx⟩ := exists_hasDerivAt_eq_zero l cf.continuousOn (fb.trans fa.symm) (fun s _=>df s)
    refine ⟨x,hx.2.ne,?_,dx⟩
    rw [abs_of_neg (sub_neg.mpr l)] at bd
    rw [abs_of_neg (sub_neg.mpr hx.2)]; linarith only [hx.1,bd]
  · obtain ⟨x,hx,dx⟩ := exists_hasDerivAt_eq_zero l cf.continuousOn (fa.trans fb.symm) (fun s _=>df s)
    refine ⟨x,hx.1.ne',?_,dx⟩
    rw [abs_of_pos (sub_pos.mpr l)] at bd
    rw [abs_of_pos (sub_pos.mpr hx.1)]; linarith only [hx.2,bd]

/-- At an accumulation of vertical tangencies the elastic force and its
first arclength derivative vanish. The Frenet data are in arclength. -/
theorem flat_force {z Y k p q w : ℝ→ℝ} {a : ℝ}
    (dz : ∀s,HasDerivAt z (-k s*Y s) s) (dy : ∀s,HasDerivAt Y (k s*z s) s)
    (dk : ∀s,HasDerivAt k (p s) s) (dp : ∀s,HasDerivAt p (q s) s)
    (dq : ∀s,HasDerivAt q (w s) s) (cw : Continuous w) (ya : Y a≠0)
    (zero : accumulatingZeros z a) :
    q a+(k a)^3/2=0 ∧ w a+(3/2:ℝ)*(k a)^2*p a=0 := by
  have cy := continuous_iff_continuousAt.mpr (fun s=>(dy s).continuousAt)
  have ym : ∀ᶠ s in nhds a,Y s≠0 := cy.continuousAt.eventually_ne ya
  obtain ⟨r,rp,ring⟩ := Metric.mem_nhds_iff.mp ym
  have first := rolle_at_accumulating_zeros dz zero
  have kz : accumulatingZeros k a := by
    intro d dd
    obtain ⟨b,ba,bd,eq⟩ := first (min d r) (lt_min dd rp)
    have yn : Y b≠0 := ring (show b∈Metric.ball a r from bd.trans_le (min_le_right ..))
    refine ⟨b,ba,bd.trans_le (min_le_left ..),?_⟩
    have z' := (mul_eq_zero.mp eq).resolve_right yn
    exact neg_eq_zero.mp z'
  have pz := rolle_at_accumulating_zeros dk kz
  have qz := rolle_at_accumulating_zeros dp pz
  have wz := rolle_at_accumulating_zeros dq qz
  have ka := value_at_accumulating_zeros (dk a).continuousAt kz
  have qa := value_at_accumulating_zeros (dq a).continuousAt qz
  have wa := value_at_accumulating_zeros cw.continuousAt wz
  simp [ka,qa,wa]

end MigrationGeometry.AngularExcursion
#print axioms MigrationGeometry.AngularExcursion.flat_force
