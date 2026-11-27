import SolitonClassification.MeromorphicIdentityPlane
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.Ring.Periodic

noncomputable section
open Complex Set Filter Function
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

/-- A real curvature admitting a globally meromorphic continuation with a
nonreal period. The closed curve itself supplies the horizontal period.
At a pole the standard complex-valued representative takes value zero. -/
structure EllipticExtension (k : ℝ → ℝ) where
  extension : ℂ → ℂ
  normal : ∀z, MeromorphicNFAt extension z
  analytic_real : ∀s : ℝ, AnalyticAt ℂ extension (s:ℂ)
  restrict_real : ∀s : ℝ, extension (s:ℂ)=(k s:ℂ)
  transverse : ∃v : ℂ, v.im≠0 ∧ Periodic extension v

theorem EllipticExtension.periodic_real {k : ℝ → ℝ} (e : EllipticExtension k)
    {P : ℝ} (h : Periodic k P) : Periodic e.extension (P:ℂ) := by
  let f := fun z : ℂ => e.extension (z+(P:ℂ))
  have fn (x : ℂ) : MeromorphicNFAt f x :=
    meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt.mpr (e.normal _)
  have hm (x : ℂ) : MeromorphicAt (fun z=>f z-e.extension z) x :=
    (fn x).meromorphicAt.sub (e.normal x).meromorphicAt
  have hr (s : ℝ) : f (s:ℂ)-e.extension (s:ℂ)=0 := by
    dsimp [f]
    rw [←Complex.ofReal_add,e.restrict_real,e.restrict_real,h s,sub_self]
  intro z
  have zero := real_axis_meromorphic_identity hm hr z
  have localEq : f =ᶠ[𝓝[≠] z] e.extension := zero.mono (fun _ h0=>sub_eq_zero.mp h0)
  exact (((fn z).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (e.normal z)).mp localEq).eq_of_nhds

theorem EllipticExtension.periodic_upper {k : ℝ → ℝ} (e : EllipticExtension k) :
    ∃v : ℂ, 0<v.im ∧ Periodic e.extension v := by
  obtain ⟨v,hv,hp⟩ := e.transverse
  rcases lt_or_gt_of_ne hv with h|h
  · exact ⟨-v,by simpa using h,hp.neg⟩
  · exact ⟨v,h,hp⟩

theorem restriction_derivative {f : ℂ → ℂ} {k : ℝ → ℝ}
    (ha : ∀s : ℝ,AnalyticAt ℂ f (s:ℂ)) (he : ∀s : ℝ,f (s:ℂ)=(k s:ℂ))
    (s : ℝ) : deriv f (s:ℂ)=((deriv k s : ℝ):ℂ) := by
  have dc := (ha s).differentiableAt.hasDerivAt.comp_ofReal
  have de : HasDerivAt (fun u : ℝ=>(k u:ℂ)) (deriv f (s:ℂ)) s := by
    simpa only [he] using dc
  have rr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s de
  change HasDerivAt k (deriv f (s:ℂ)).re s at rr
  exact de.unique rr.differentiableAt.hasDerivAt.ofReal_comp

end ClosedSimilarity.MeromorphicCurvature

