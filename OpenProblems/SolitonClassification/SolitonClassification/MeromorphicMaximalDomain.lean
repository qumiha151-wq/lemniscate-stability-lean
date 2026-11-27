import SolitonClassification.MeromorphicConnectedIdentity
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Topology.MetricSpace.Perfect

noncomputable section
open Complex Filter Set Function
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

/-- A meromorphic filling agrees pointwise with the original normalized
function on ordinary points near x. It may assign new values on S. -/
def LocalFill (S : Set ℂ) (f g : ℂ→ℂ) (x : ℂ) : Prop :=
  (∀ᶠ y in 𝓝 x,MeromorphicNFAt g y) ∧ (∀ᶠ y in 𝓝 x,y∉S → g y=f y)

def fillDomain (S : Set ℂ) (f : ℂ→ℂ) : Set ℂ := {x | ∃g,LocalFill S f g x}

theorem LocalFill.nearby {S : Set ℂ} {f g : ℂ→ℂ} {x : ℂ} (h : LocalFill S f g x) :
    ∀ᶠ y in 𝓝 x,LocalFill S f g y := h.1.eventually_nhds.and h.2.eventually_nhds

theorem fillDomain_open (S : Set ℂ) (f : ℂ→ℂ) : IsOpen (fillDomain S f) := by
  apply isOpen_iff_eventually.mpr
  rintro x ⟨g,hg⟩
  exact hg.nearby.mono (fun _ ht=>⟨g,ht⟩)

theorem LocalFill.unique {S : Set ℂ} (sC : S.Countable) {f g h : ℂ→ℂ} {x : ℂ}
    (hg : LocalFill S f g x) (hh : LocalFill S f h x) : g =ᶠ[𝓝 x] h := by
  have gn : MeromorphicNFAt g x := hg.1.self_of_nhds
  have hn : MeromorphicNFAt h x := hh.1.self_of_nhds
  apply (gn.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hn).mp
  apply (gn.meromorphicAt.frequently_eq_iff_eventuallyEq hn.meromorphicAt).mp
  have gf := (hg.2.and hh.2).filter_mono (show 𝓝[≠] x≤𝓝 x from nhdsWithin_le_nhds)
  exact ((frequently_outside_countable sC x).and_eventually gf).mono
    (fun y hy=>(hy.2.1 hy.1).trans (hy.2.2 hy.1).symm)

open Classical in
def maximalFill (S : Set ℂ) (f : ℂ→ℂ) (x : ℂ) : ℂ :=
  if h : x∈fillDomain S f then (Classical.choose h) x else 0

theorem LocalFill.maximal_germ {S : Set ℂ} (sC : S.Countable) {f g : ℂ→ℂ} {x : ℂ}
    (rep : LocalFill S f g x) : maximalFill S f =ᶠ[𝓝 x] g := by
  classical
  filter_upwards [rep.nearby] with y hy
  have domain : y∈fillDomain S f := ⟨g,hy⟩
  rw [maximalFill,dif_pos domain]
  exact (LocalFill.unique sC (Classical.choose_spec domain) hy).eq_of_nhds

theorem maximal_normal {S : Set ℂ} (sC : S.Countable) {f : ℂ→ℂ} {x : ℂ}
    (hx : x∈fillDomain S f) : MeromorphicNFAt (maximalFill S f) x := by
  obtain ⟨g,hg⟩:=hx
  exact (meromorphicNFAt_congr (hg.maximal_germ sC)).mpr hg.1.self_of_nhds

theorem original_fills {S : Set ℂ} (closed : IsClosed S) {f : ℂ→ℂ}
    (nf : ∀x∉S,MeromorphicNFAt f x) {x : ℂ} (hx : x∉S) : LocalFill S f f x :=
  ⟨(show ∀ᶠ z in 𝓝 x,z∉S from closed.isOpen_compl.mem_nhds hx).mono (fun z nz=>nf z nz),
    Eventually.of_forall (fun _ _=>rfl)⟩

/-- A nonempty closed countable subset of the plane has an isolated point. -/
theorem countable_closed_isolated {S : Set ℂ} (closed : IsClosed S) (sC : S.Countable)
    (ne : S.Nonempty) : ∃x∈S,∀ᶠ y in 𝓝[≠] x,y∉S := by
  by_contra! no
  have perf : Perfect S := ⟨closed,fun x hx=>accPt_iff_frequently_nhdsNE.mpr (no x hx)⟩
  obtain ⟨i,sub,_,inj⟩:=perf.exists_nat_bool_injection ne
  have count := (sC.mono sub).preimage inj
  have : Countable (ℕ→Bool) := Set.countable_univ_iff.mp (by simpa only [preimage_range] using count)
  obtain ⟨g,sur⟩:=exists_surjective_nat (ℕ→Bool)
  obtain ⟨n,hn⟩:=sur (fun j=> !(g j j))
  have ee:=congrFun hn n
  cases h:g n n <;> simp [h] at ee

end ClosedSimilarity.MeromorphicCurvature

