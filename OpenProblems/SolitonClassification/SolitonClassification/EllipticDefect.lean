import SolitonClassification.EllipticPeriodPlane
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
open Complex Set Filter Function
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

def curvatureDefect (k : ℂ → ℂ) (z : ℂ) : ℂ := deriv (deriv k) z + 2*(k z)^3/9

open Classical in
def regularDefect (k : ℂ → ℂ) (z : ℂ) : ℂ :=
  if AnalyticAt ℂ k z then curvatureDefect k z else 0

theorem analytic_curvatureDefect {k : ℂ → ℂ} {x : ℂ} (h : AnalyticAt ℂ k x) :
    AnalyticAt ℂ (curvatureDefect k) x := by
  unfold curvatureDefect
  exact h.deriv.deriv.add ((analyticAt_const.mul (h.pow 3)).div analyticAt_const (by norm_num))

theorem analytic_period_iff {k : ℂ → ℂ} {v : ℂ} (hp : Periodic k v) (x : ℂ) :
    AnalyticAt ℂ k (x+v) ↔ AnalyticAt ℂ k x := by
  constructor
  · intro h
    have inner : AnalyticAt ℂ (fun z : ℂ => z+v) x := analyticAt_id.add analyticAt_const
    have H := h.comp (f:=fun z : ℂ => z+v) inner
    change AnalyticAt ℂ (fun z=>k (z+v)) x at H
    rwa [show (fun z=>k (z+v))=k from funext hp] at H
  · intro h
    have h' : AnalyticAt ℂ k ((x+v)+(-v)) := by simpa using h
    have inner : AnalyticAt ℂ (fun z : ℂ => z+(-v)) (x+v) := analyticAt_id.add analyticAt_const
    have H := h'.comp (f:=fun z : ℂ => z+(-v)) inner
    change AnalyticAt ℂ (fun z=>k (z+(-v))) (x+v) at H
    rwa [show (fun z=>k (z+(-v)))=k from funext hp.neg] at H

theorem deriv_period {k : ℂ → ℂ} {v : ℂ} (hp : Periodic k v) : Periodic (deriv k) v := by
  intro x
  calc deriv k (x+v) = deriv (fun z=>k (z+v)) x := (deriv_comp_add_const k v x).symm
       _ = deriv k x := by rw [show (fun z=>k (z+v))=k from funext hp]

theorem regularDefect_period {k : ℂ → ℂ} {v : ℂ} (hp : Periodic k v) :
    Periodic (regularDefect k) v := by
  intro x
  classical
  simp only [regularDefect,analytic_period_iff hp,curvatureDefect,hp x,deriv_period (deriv_period hp) x]

/-- Fill the isolated poles with the value of the removable defect. -/
theorem regularDefect_entire {k : ℂ → ℂ} (hm : ∀x,MeromorphicAt k x)
    (rem : ∀x, ¬AnalyticAt ℂ k x → ∃g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x=0 ∧
      curvatureDefect k =ᶠ[𝓝[≠] x] g) : Differentiable ℂ (regularDefect k) := by
  intro x
  classical
  apply AnalyticAt.differentiableAt
  by_cases h : AnalyticAt ℂ k x
  · apply (analyticAt_congr _).mpr (analytic_curvatureDefect h)
    filter_upwards [h.eventually_analyticAt] with z hz
    simp [regularDefect,hz]
  · obtain ⟨g,ag,gx,ge⟩ := rem x h
    apply (analyticAt_congr _).mpr ag
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE _ (by simp [regularDefect,h,gx])
    filter_upwards [(hm x).eventually_analyticAt,ge] with z hz he
    simpa [regularDefect,hz] using he

/-- An elliptic curvature with the stated local pole cancellation is either
constant or has identically vanishing defect on its regular set. -/
theorem elliptic_defect_dichotomy {k : ℂ → ℂ} {P : ℝ} {v : ℂ}
    (hm : ∀x,MeromorphicAt k x) (hp : 0<P) (hv : 0<v.im)
    (hP : Periodic k (P:ℂ)) (hV : Periodic k v)
    (rem : ∀x, ¬AnalyticAt ℂ k x → ∃g : ℂ → ℂ, AnalyticAt ℂ g x ∧ g x=0 ∧
      curvatureDefect k =ᶠ[𝓝[≠] x] g) :
    (∀z,k z=k 0) ∨ ∀z,AnalyticAt ℂ k z → curvatureDefect k z=0 := by
  classical
  by_cases all : ∀x,AnalyticAt ℂ k x
  · exact Or.inl (fun z=>entire_two_periods_constant (fun x=>(all x).differentiableAt) hp hv hP hV z 0)
  · obtain ⟨x,hx⟩ := not_forall.mp all
    right
    intro z hz
    have eq := entire_two_periods_constant (regularDefect_entire hm rem) hp hv
      (regularDefect_period hP) (regularDefect_period hV) z x
    simpa [regularDefect,hz,hx] using eq

end ClosedSimilarity.MeromorphicCurvature

