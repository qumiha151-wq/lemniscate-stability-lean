import SolitonClassification.MeromorphicIdentityPlane
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.Cardinality

noncomputable section
open Complex Filter Set
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

private theorem germSet_open {p : ℂ → Prop} : IsOpen {x | ∀ᶠ y in 𝓝[≠] x, p y} := by
  rw [isOpen_iff_eventually]
  intro x hx
  apply (eventually_nhdsWithin_iff.mp (eventually_nhdsNE_eventually_nhds_iff.mpr hx)).mono
  intro y hy
  by_cases ey : y=x
  · simpa [ey] using hx
  · exact eventually_nhdsWithin_of_eventually_nhds (hy ey)

theorem identity_connected_germs {U : Set ℂ} (conn : IsPreconnected U)
    {f g : ℂ → ℂ} (mf : ∀x∈U, MeromorphicAt f x) (mg : ∀x∈U,MeromorphicAt g x)
    {x : ℂ} (xx : x∈U) (germ : f =ᶠ[𝓝[≠] x] g) {z : ℂ} (zz : z∈U) :
    f =ᶠ[𝓝[≠] z] g := by
  let A:={v : ℂ | f =ᶠ[𝓝[≠] v] g}
  let B:={v : ℂ | ∀ᶠ w in 𝓝[≠] v,f w≠g w}
  have cover : U⊆A∪B := by
    intro t ht
    obtain le|ne:=((mf t ht).sub (mg t ht)).eventually_eq_zero_or_eventually_ne_zero
    · exact Or.inl (le.mono (fun _ eq=>sub_eq_zero.mp eq))
    · exact Or.inr (ne.mono (fun _ neq e=>neq (sub_eq_zero.mpr e)))
  by_contra no
  have bin : z∈B := (cover zz).resolve_left no
  obtain ⟨p,_,ha,hb⟩:=conn A B germSet_open germSet_open cover ⟨x,xx,germ⟩ ⟨z,zz,bin⟩
  obtain ⟨t,eq,ne⟩:=((show ∀ᶠ t in 𝓝[≠] p,f t=g t from ha).and hb).exists
  exact ne eq

theorem countable_complement_connected {S : Set ℂ} (hS : S.Countable) : IsPreconnected Sᶜ := by
  exact (hS.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex];norm_num)).isConnected.2

theorem frequently_outside_countable {S : Set ℂ} (hS : S.Countable) (x : ℂ) :
    ∃ᶠ z in 𝓝[≠] x,z∉S := by
  have dense := (hS.insert x).dense_compl ℂ
  have near : ∃ᶠ z in 𝓝 x,z∈(insert x S)ᶜ := mem_closure_iff_frequently.mp (dense x)
  intro no
  have eventual:=eventually_nhdsWithin_iff.mp no
  obtain ⟨z,hz,imp⟩ := (near.and_eventually eventual).exists
  exact (imp (fun eq=>hz (Or.inl eq))) (fun zs=>hz (Or.inr zs))

end ClosedSimilarity.MeromorphicCurvature

