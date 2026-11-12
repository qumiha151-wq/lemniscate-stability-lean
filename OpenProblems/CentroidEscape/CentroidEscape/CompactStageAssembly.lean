import CentroidEscape.VariableOrderCertificate

/-!
A short proof constructor for a finite list of already checked stages.
It performs no coefficient arithmetic and adds no numerical hypothesis:
each extension requires the actual proof of the next stage.
-/
namespace CentroidEscape

theorem checkedStagesExtend (P : ℕ → Prop) (n : ℕ)
    (h : ∀ i<n, P i) (hn : P n) : ∀ i<n+1, P i := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · exact h i hlt
  · exact hn

end CentroidEscape

#print axioms CentroidEscape.checkedStagesExtend
