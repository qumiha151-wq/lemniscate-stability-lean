import SolitonClassification.CountableSingularityFilling
import SolitonClassification.MeromorphicClosedProfile

noncomputable section
open Complex Filter Set
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

/-- The signed arclength curvature admits a single-valued meromorphic extension
away from a closed countable complex exceptional set disjoint from real arclength.
Ordinary poles outside that set are allowed. -/
def CountableExceptionalTrace (k : ℝ→ℝ) : Prop :=
  ∃(S : Set ℂ) (f : ℂ→ℂ),IsClosed S ∧ S.Countable ∧ (∀t : ℝ,(t:ℂ)∉S) ∧
    MeromorphicOn f Sᶜ ∧ (∀t : ℝ,AnalyticAt ℂ f (t:ℂ)) ∧ ∀t : ℝ,f (t:ℂ)=(k t:ℂ)

/-- The equation fills the entire exceptional set, even when it has nonisolated points. -/
theorem countable_exceptional_trace_iff_global {a b L : ℝ} (p : PeriodicSupportProfile a b L)
    (hL : 0<L) : CountableExceptionalTrace p.k ↔ GlobalMeromorphicTrace p.k := by
  constructor
  · rintro ⟨S,f,closed,sC,regular,mer,an,rep⟩
    let F:=toMeromorphicNFOn f Sᶜ
    have nf : ∀x∉S,MeromorphicNFAt F x := fun x hx=>meromorphicNFOn_toMeromorphicNFOn f Sᶜ hx
    have germs (t : ℝ) : F =ᶠ[𝓝 (t:ℂ)] f :=
      ((nf _ (regular t)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (an t).meromorphicNFAt).mp
        (mer.toMeromorphicNFOn_eq_self_on_nhdsNE (regular t))
    have normReal (t : ℝ) : AnalyticAt ℂ F (t:ℂ) := (analyticAt_congr (germs t)).mpr (an t)
    have traceF (t : ℝ) : F (t:ℂ)=(p.k t:ℂ) := (germs t).eq_of_nhds.trans (rep t)
    have all:=all_filled_of_isolated_repair closed sC nf (fun x _ near=>
      ordinary_isolated_repair (p.dilation_pos hL) x (near.mono (fun y hy=>
        ⟨maximal_normal sC hy,residual_on_fillDomain p closed sC regular nf normReal traceF hy⟩)))
    have agrees (t : ℝ) : maximalFill S F =ᶠ[𝓝 (t:ℂ)] F :=
      (original_fills closed nf (regular t)).maximal_germ sC
    exact ⟨maximalFill S F,fun x=>(maximal_normal sC (all x)).meromorphicAt,
      fun t=>(analyticAt_congr (agrees t)).mpr (normReal t),
      fun t=>(agrees t).eq_of_nhds.trans (traceF t)⟩
  · rintro ⟨f,m,an,rep⟩
    exact ⟨∅,f,isClosed_empty,countable_empty,fun _=>notMem_empty _,fun x _=>m x,an,rep⟩

theorem countable_exceptional_curvature_iff {a b L : ℝ} (p : PeriodicSupportProfile a b L)
    (hL : 0<L) : CountableExceptionalTrace p.k ↔
    (∃K : ℝ,K≠0 ∧ ∀t,p.k t=K) ∨ (∀t,deriv (deriv p.k) t+2/9*p.k t^3=0) :=
  (countable_exceptional_trace_iff_global p hL).trans (meromorphic_curvature_iff p hL)

end ClosedSimilarity.MeromorphicCurvature
namespace ClosedSimilarity.ClosedUnitFrenetCurve
open MeromorphicCurvature

/-- Actual position classification for closed similarity immersions whose curvature
admits a single-valued meromorphic continuation outside a closed countable set. -/
theorem countable_exceptional_circle_or_bernoulli (c : ClosedUnitFrenetCurve) (a b vx vy : ℝ)
    (law : ∀s,c.positionForce s= -a*c.normalSupport s-b*c.tangentSupport s+
      vx*c.ty s-vy*c.tx s) (extn : CountableExceptionalTrace c.k) :
    (∃(K : ℝ) (O Z : ℂ), K≠0 ∧ Z≠0 ∧ (∀s,c.k s=K) ∧
      ∀s:ℝ,(c.x s:ℂ)+(c.y s:ℂ)*I=O+Z*exp (((K*s:ℝ):ℂ)*I)) ∨
      (b=0 ∧ BernoulliGeometry.IsBernoulliCover c a vx vy) := by
  obtain ⟨p,hk⟩:=c.exists_centered_profile_with_curvature a b vx vy law
  have traceP : CountableExceptionalTrace p.k := hk ▸ extn
  have mg:=(countable_exceptional_trace_iff_global p c.period_pos).mp traceP
  exact c.meromorphic_curvature_circle_or_bernoulli a b vx vy law (hk ▸ mg)

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.MeromorphicCurvature.countable_exceptional_curvature_iff
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.countable_exceptional_circle_or_bernoulli

