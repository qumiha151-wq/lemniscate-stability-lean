import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set
namespace ClosedSimilarity.QuarterReflection

private theorem fold_half {E : Type*} {g : ℝ → E} {q : E} {S t : ℝ}
    (reflect : ∀ t, g (2*S-t)=q ↔ g t=q) (ht : t∈Icc 0 (2*S)) (hit : g t=q) :
    ∃ u∈Icc 0 S, g u=q ∧ (t=u ∨ t=2*S-u) := by
  obtain ⟨lo,hi⟩ := ht
  by_cases first : t≤S
  · exact ⟨t,⟨lo,first⟩,hit,Or.inl rfl⟩
  · exact ⟨2*S-t,⟨by linarith,by linarith⟩,(reflect t).2 hit,Or.inr (by ring)⟩

/-- If a target has a unique preimage in the first quarter and its opposite
    is omitted there, the full four-quarter traversal has exactly two labels. -/
theorem exact_labels {E : Type*} [AddGroup E] {g : ℝ → E} {p : E} {S r : ℝ}
    (per : Function.Periodic g (4*S)) (odd : ∀ t, g (-t) = -g t)
    (positive : ∀ t, g (2*S-t)=p ↔ g t=p) (negative : ∀ t, g (2*S-t)= -p ↔ g t= -p)
    (inside : r∈Ioo 0 S) (at_r : g r=p)
    (unique : ∀ t∈Icc 0 S, g t=p → t=r) (avoid : ∀ t∈Icc 0 S, g t≠ -p) :
    ∀ t∈Ico 0 (4*S), g t=p ↔ t=r ∨ t=2*S-r := by
  intro t ht
  obtain ⟨lo,hi⟩ := ht
  constructor
  · intro hit
    by_cases early : t≤2*S
    · obtain ⟨u,hu,seen,label⟩ := fold_half positive ⟨lo,early⟩ hit
      rwa [unique u hu seen] at label
    · have other : g (4*S-t) = -p := by
        rw [show 4*S-t = -t+(4*S) by ring,per,odd,hit]
      obtain ⟨u,hu,seen,_⟩ := fold_half negative
        (show 4*S-t∈Icc 0 (2*S) from ⟨by linarith,by linarith⟩) other
      exact (avoid u hu seen).elim
  · rintro (rfl | rfl)
    · exact at_r
    · exact (positive r).2 at_r

/-- Two labels strictly in the first half of a period rule out every
    shorter period. The conclusion only involves positions. -/
theorem least_period_of_labels {E : Type*} {g : ℝ → E} {p : E} {S r : ℝ}
    (per : Function.Periodic g (4*S)) (inside : r∈Ioo 0 S)
    (labels : ∀ t∈Ico 0 (4*S), g t=p ↔ t=r ∨ t=2*S-r) :
    IsLeast {d : ℝ | 0<d ∧ Function.Periodic g d} (4*S) := by
  obtain ⟨lo,hi⟩ := inside
  have last : g (2*S-r)=p := (labels _ ⟨by linarith,by linarith⟩).2 (Or.inr rfl)
  have exclude (h : ℝ) (hp : 0<h) (short : h≤2*S) (ph : Function.Periodic g h) : False := by
    have next := (labels (2*S-r+h) ⟨by linarith,by linarith⟩).1 ((ph _).trans last)
    rcases next with eq | eq <;> linarith
  refine ⟨⟨by linarith,per⟩,?_⟩
  intro d hd
  obtain ⟨dp,pd⟩ := hd
  by_contra! small
  by_cases half : d≤2*S
  · exact exclude d dp half pd
  · exact exclude (4*S-d) (by linarith) (by linarith) (per.sub_period pd)

/-- The four-quarter period of a curve with the stated first-quarter
    unique target is its least positive position period. -/
theorem least_period {E : Type*} [AddGroup E] {g : ℝ → E} {p : E} {S r : ℝ}
    (per : Function.Periodic g (4*S)) (odd : ∀ t, g (-t) = -g t)
    (positive : ∀ t, g (2*S-t)=p ↔ g t=p) (negative : ∀ t, g (2*S-t)= -p ↔ g t= -p)
    (inside : r∈Ioo 0 S) (at_r : g r=p)
    (unique : ∀ t∈Icc 0 S, g t=p → t=r) (avoid : ∀ t∈Icc 0 S, g t≠ -p) :
    IsLeast {d : ℝ | 0<d ∧ Function.Periodic g d} (4*S) :=
  least_period_of_labels per inside (exact_labels per odd positive negative inside at_r unique avoid)

end ClosedSimilarity.QuarterReflection
#print axioms ClosedSimilarity.QuarterReflection.exact_labels
#print axioms ClosedSimilarity.QuarterReflection.least_period
