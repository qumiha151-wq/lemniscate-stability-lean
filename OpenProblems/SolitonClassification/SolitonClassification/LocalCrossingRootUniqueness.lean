import SolitonClassification.CrossingStressResponse
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Filter Set Metric MeasureTheory
open scoped Topology
namespace ClosedSimilarity.CrossingResponse

private theorem primitive_derivative (F : ℝ → ℝ → ℝ)
    (cont : Continuous (fun z : ℝ × ℝ => F z.1 z.2)) (e t : ℝ) :
    HasDerivAt (fun x => ∫ z in (0:ℝ)..x, F e z) (F e t) t := by
  have c : Continuous (F e) := cont.comp (show Continuous (fun x : ℝ => (e,x)) from
    continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_hasDerivAt_right (c.intervalIntegrable 0 t)
    c.aestronglyMeasurable.stronglyMeasurableAtFilter c.continuousAt

private theorem cont_direction {f g : ℝ → ℝ → ℝ}
    (cf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) (cg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => f p.1.1 p.2 - p.1.2 * g p.1.1 p.2) := by
  have proj : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  exact (cf.comp proj).sub ((continuous_snd.comp continuous_fst).mul (cg.comp proj))

/-- A fixed parameter window about any simple frozen crossing contains at
most one perturbed axis root for every sufficiently small perturbation. -/
theorem eventually_injOn_signed_axis {a : ℝ} (simple : V 0 a ≠ 0)
    (e β : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) (hβ : Tendsto β atTop (𝓝 0)) :
    ∃ d > 0, ∀ᶠ n in atTop, Set.InjOn (fun t => X (e n) t - β n * Y (e n) t)
      (Ioo (a-d) (a+d)) := by
  let D (p : (ℝ × ℝ) × ℝ) := tx p.1.1 p.2 - p.1.2 * ty p.1.1 p.2
  have cD : Continuous D := cont_direction (f := tx) (g := ty) tx_cont ty_cont
  have Dne : D ((0,0),a) ≠ 0 := by simpa [D,(frozen_tangent a).1] using simple
  have h := (cD.tendsto ((0,0),a)).eventually_ne Dne
  obtain ⟨u,hu,J,hJ,region⟩ := mem_nhds_prod_iff.mp h
  obtain ⟨d,hd,win⟩ := Metric.mem_nhds_iff.mp hJ
  refine ⟨d,hd,?_⟩
  filter_upwards [(he.prodMk_nhds hβ).eventually hu] with n param
  let F (t : ℝ) := X (e n) t - β n * Y (e n) t
  have df (t : ℝ) : HasDerivAt F (D ((e n,β n),t)) t :=
    (primitive_derivative tx tx_cont (e n) t).sub ((primitive_derivative ty ty_cont (e n) t).const_mul (β n))
  have impossible {x y : ℝ} (hx : x ∈ Ioo (a-d) (a+d)) (hy : y ∈ Ioo (a-d) (a+d))
      (lt : x < y) (eqn : F x = F y) : False := by
    have cf : Continuous F := continuous_iff_continuousAt.mpr (fun t => (df t).continuousAt)
    obtain ⟨t,ht,zero⟩ := exists_hasDerivAt_eq_zero lt cf.continuousOn eqn (fun t _ => df t)
    have bt : t ∈ Metric.ball a d := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith [hx.1,hy.2,ht.1,ht.2]
    exact (region (show ((e n,β n),t) ∈ u ×ˢ J from ⟨param,win bt⟩)) zero
  intro x hx y hy eqn
  rcases lt_trichotomy x y with lt | eq | gt
  · exact (impossible hx hy lt eqn).elim
  · exact eq
  · exact (impossible hy hx gt eqn.symm).elim

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.eventually_injOn_signed_axis
