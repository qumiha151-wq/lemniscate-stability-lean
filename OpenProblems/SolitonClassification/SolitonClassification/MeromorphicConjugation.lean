import SolitonClassification.MeromorphicIdentityPlane
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open Complex ComplexConjugate Filter Set Function
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

def conjugateTrace (f : ℂ → ℂ) (z : ℂ) : ℂ := conj (f (conj z))

theorem conjugateTrace_hasDeriv {f : ℂ → ℂ} {x d : ℂ} (hd : HasDerivAt f d (conj x)) :
    HasDerivAt (conjugateTrace f) (conj d) x := by
  have pt : Tendsto (conj:ℂ→ℂ) (𝓝[≠] x) (𝓝[≠] (conj x)) := by
    apply Complex.continuous_conj.continuousWithinAt.tendsto_nhdsWithin
    intro z hz
    exact fun eq=>hz ((starRingEnd ℂ).injective eq)
  rw [hasDerivAt_iff_tendsto_slope] at hd ⊢
  have tr := Complex.continuous_conj.continuousAt.tendsto.comp (hd.comp pt)
  convert tr using 1
  funext z
  simp [Function.comp_def,slope_def_field,conjugateTrace]

theorem conjugateTrace_analytic {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f (conj x)) :
    AnalyticAt ℂ (conjugateTrace f) x := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have near := Complex.continuous_conj.continuousAt.tendsto.eventually
    (Complex.analyticAt_iff_eventually_differentiableAt.mp hf)
  filter_upwards [near] with z hz
  exact (conjugateTrace_hasDeriv hz.hasDerivAt).differentiableAt

theorem conjugateTrace_normal {f : ℂ → ℂ} {x : ℂ} (nf : MeromorphicNFAt f (conj x)) :
    MeromorphicNFAt (conjugateTrace f) x := by
  rcases nf with h|⟨n,g,ag,gn,eq⟩
  · left
    filter_upwards [Complex.continuous_conj.continuousAt.tendsto.eventually h] with t ht
    change f (conj t)=0 at ht
    simp [conjugateTrace,ht]
  · refine Or.inr ⟨n,conjugateTrace g,conjugateTrace_analytic ag,?_,?_⟩
    · simpa [conjugateTrace] using gn
    · filter_upwards [Complex.continuous_conj.continuousAt.tendsto.eventually eq] with z hz
      change f (conj z)=(conj z-conj x)^n*g (conj z) at hz
      change conj (f (conj z))=(z-x)^n*conj (g (conj z))
      simp [hz]

theorem normal_eq_of_trace {f g : ℂ → ℂ} (nf : ∀z,MeromorphicNFAt f z)
    (ng : ∀z,MeromorphicNFAt g z) (h : ∀s : ℝ,f (s:ℂ)=g (s:ℂ)) : f=g := by
  have eq := real_axis_meromorphic_identity (f:=fun z=>f z-g z)
    (fun z=>(nf z).meromorphicAt.sub (ng z).meromorphicAt) (fun s=>sub_eq_zero.mpr (h s))
  funext z
  exact (((nf z).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (ng z)).mp
    ((eq z).mono (fun _ e=>sub_eq_zero.mp e))).eq_of_nhds

theorem normal_conj_symmetry {f : ℂ → ℂ} {k : ℝ → ℝ}
    (nf : ∀z,MeromorphicNFAt f z) (realEq : ∀t : ℝ,f (t:ℂ)=(k t:ℂ)) (z : ℂ) :
    f (conj z)=conj (f z) := by
  have eq : conjugateTrace f=f := normal_eq_of_trace (fun x=>conjugateTrace_normal (nf _))
    nf (fun s=>by simp [conjugateTrace,realEq])
  have e := congrFun eq (conj z)
  simpa [conjugateTrace] using e.symm

end ClosedSimilarity.MeromorphicCurvature

