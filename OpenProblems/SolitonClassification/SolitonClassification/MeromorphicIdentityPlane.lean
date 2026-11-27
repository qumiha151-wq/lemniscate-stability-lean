import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Complex Set Filter
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

private theorem germ_open {p : ℂ → Prop} : IsOpen {x | ∀ᶠ y in 𝓝[≠] x, p y} := by
  rw [isOpen_iff_eventually]
  intro x hx
  apply eventually_nhdsWithin_iff.mp (eventually_nhdsNE_eventually_nhds_iff.mpr hx) |>.mono
  intro y hy
  by_cases ey : y=x
  · simpa [ey] using hx
  · exact eventually_nhdsWithin_of_eventually_nhds (hy ey)

/-- The identity theorem in terms of punctured germs; actual values at isolated poles
or at non-normalized removable singularities are immaterial. -/
theorem meromorphic_identity_plane {f : ℂ → ℂ} (hm : ∀z, MeromorphicAt f z)
    {x : ℂ} (hx : ∀ᶠ z in 𝓝[≠] x, f z=0) (y : ℂ) : ∀ᶠ z in 𝓝[≠] y, f z=0 := by
  let S := {z : ℂ | ∀ᶠ w in 𝓝[≠] z, f w=0}
  have openS : IsOpen S := germ_open
  have compS : Sᶜ = {z : ℂ | ∀ᶠ w in 𝓝[≠] z, f w≠0} := by
    ext z
    change (¬(∀ᶠ w in 𝓝[≠] z, f w=0)) ↔ ∀ᶠ w in 𝓝[≠] z, f w≠0
    constructor
    · exact (hm z).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    · intro nz zz
      obtain ⟨_,h1,h2⟩ := (nz.and zz).exists
      exact h1 h2
  have cover : S=univ := IsClopen.eq_univ ⟨isOpen_compl_iff.mp (compS ▸ germ_open),openS⟩ ⟨x,hx⟩
  exact show y∈S from cover ▸ mem_univ y

theorem real_axis_meromorphic_identity {f : ℂ → ℂ} (hm : ∀z, MeromorphicAt f z)
    (hr : ∀t : ℝ, f (t:ℂ)=0) (y : ℂ) : ∀ᶠ z in 𝓝[≠] y, f z=0 := by
  apply meromorphic_identity_plane hm (x:=0) _ y
  apply ((hm 0).frequently_zero_iff_eventuallyEq_zero).mp
  have tends : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    intro t ht
    simpa using ht
  by_contra! h
  obtain ⟨t,hne⟩ := (tends.eventually h).exists
  exact hne (hr t)

end ClosedSimilarity.MeromorphicCurvature

