import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.Ring

/-! Periods of a continuous time path modulo compact spatial symmetries. -/

namespace SolitonClassification.ReturnScales

open Set

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/-- Time shifts realized by one spatial group element along the entire path. -/
def shifts (Y : ℝ → X) : AddSubgroup ℝ where
  carrier := {h | ∃ v : G, ∀ y, Y (y+h) = v • Y y}
  zero_mem' := ⟨1, fun y => by simp⟩
  add_mem' := by
    rintro h k ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨v*u, fun y => by rw [← add_assoc, hv, hu, mul_smul]⟩
  neg_mem' := by
    rintro h ⟨v, hv⟩
    refine ⟨v⁻¹, fun y => ?_⟩
    have e : Y y = v • Y (y + -h) := by simpa [add_assoc] using hv (y + -h)
    simpa using congrArg (fun x : X => v⁻¹ • x) e.symm

variable [TopologicalSpace G] [CompactSpace G] [TopologicalSpace X] [T2Space X]
  [ContinuousSMul G X] {Y : ℝ → X}

/-- Closedness uses compactness of the group of spatial multipliers. -/
theorem shifts_closed (hY : Continuous Y) : IsClosed (shifts G Y : Set ℝ) := by
  let graph : Set (ℝ × G) := ⋂ y : ℝ, {q | Y (y+q.1) = q.2 • Y y}
  have closed_graph : IsClosed graph := by
    apply isClosed_iInter
    intro y
    exact isClosed_eq (hY.comp (continuous_const.add continuous_fst))
      (continuous_snd.smul continuous_const)
  have projection : Prod.fst '' graph = (shifts G Y : Set ℝ) := by
    ext h
    change (∃ p ∈ graph, p.1 = h) ↔ ∃ v : G, ∀ y, Y (y+h) = v • Y y
    constructor
    · rintro ⟨⟨h, v⟩, hp, rfl⟩
      exact ⟨v, mem_iInter.mp hp⟩
    · rintro ⟨v, hv⟩
      exact ⟨(h,v), mem_iInter.mpr hv, rfl⟩
  rw [← projection]
  exact isClosedMap_fst_of_compactSpace _ closed_graph

/-- The log-scale subgroup is the whole line or the integer multiples of one value
    (including the trivial subgroup when that value is zero). -/
theorem shifts_top_or_cyclic (hY : Continuous Y) :
    shifts G Y = ⊤ ∨ ∃ a : ℝ, shifts G Y = AddSubgroup.zmultiples a := by
  rcases (shifts G Y).dense_or_cyclic with dense | ⟨a, ha⟩
  · left
    apply SetLike.coe_injective
    simpa only [(shifts_closed G hY).closure_eq, AddSubgroup.coe_top] using dense.closure_eq
  · exact Or.inr ⟨a, ha.trans (AddSubgroup.zmultiples_eq_closure a).symm⟩

/-- Two incommensurate shifts give a single (possibly different) spatial multiplier
    for every real shift. The criterion avoids choosing angular representatives. -/
theorem all_shifts_of_incommensurate (hY : Continuous Y) {h k : ℝ}
    (hh : h ∈ shifts G Y) (hk : k ∈ shifts G Y) (hk0 : k ≠ 0)
    (indep : ∀ m n : ℤ, n ≠ 0 → n • h ≠ m • k) (s : ℝ) :
    ∃ v : G, ∀ y, Y (y+s) = v • Y y := by
  rcases shifts_top_or_cyclic G hY with full | ⟨a, cyclic⟩
  · change s ∈ shifts G Y
    rw [full]
    trivial
  rw [cyclic] at hh hk
  obtain ⟨m, hm⟩ := hh
  obtain ⟨n, hn⟩ := hk
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hk0 (by simpa using hn.symm)
  exfalso
  apply indep m n hn0
  rw [← hm, ← hn, smul_comm]

/-- Two affine clocks representing returns commute whenever the energy on the
    physical half-line is injective and scales multiplicatively under both clocks. -/
theorem energy_forces_commuting_clocks {E f g : ℝ → ℝ} {a b : ℝ}
    (hE : Set.InjOn E (Ici 0)) (hf : ∀ t ≥ 0, 0 ≤ f t)
    (hg : ∀ t ≥ 0, 0 ≤ g t) (hEf : ∀ t ≥ 0, E (f t) = a*E t)
    (hEg : ∀ t ≥ 0, E (g t) = b*E t) {t : ℝ} (ht : 0 ≤ t) :
    f (g t) = g (f t) := by
  apply hE (hf _ (hg _ ht)) (hg _ (hf _ ht))
  rw [hEf _ (hg _ ht), hEg _ (hf _ ht), hEf _ ht, hEg _ ht]
  ring

end SolitonClassification.ReturnScales

#print axioms SolitonClassification.ReturnScales.shifts_closed
#print axioms SolitonClassification.ReturnScales.shifts_top_or_cyclic
#print axioms SolitonClassification.ReturnScales.all_shifts_of_incommensurate
#print axioms SolitonClassification.ReturnScales.energy_forces_commuting_clocks
