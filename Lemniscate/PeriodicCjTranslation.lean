import Lemniscate.NormalGraphCjEstimate

/-! A translation contributes only its size to the standard C^j norm.
This also controls the uncentered normalized curve when its translation
is the fixed center divided by the expanding scale. -/
noncomputable section
namespace Lemniscate
open Set
open scoped BigOperators

/-- Adding a constant vector changes only the zeroth derivative. Only
boundedness of that derivative is needed; all higher derivative identities
hold for the total iterated derivative without regularity assumptions. -/
theorem periodic_cj_norm_translation
    (j : ℕ) (E : ℝ → ℂ) (c : ℂ)
    (hE : BddAbove (Set.range (fun x : ℝ => ‖E x‖))) :
    periodicCjNorm j (fun x => c+E x) ≤ ‖c‖+periodicCjNorm j E := by
  have hzero : sSup (Set.range (fun x : ℝ => ‖c+E x‖)) ≤
      ‖c‖+sSup (Set.range (fun x : ℝ => ‖E x‖)) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x,rfl⟩
    exact (norm_add_le c (E x)).trans
      (add_le_add (le_refl ‖c‖) (le_csSup hE (Set.mem_range_self x)))
  have hterm (i : Fin (j+1)) :
      sSup (Set.range (fun x : ℝ => ‖iteratedDeriv i.val (fun u => c+E u) x‖)) ≤
        (if i=0 then ‖c‖ else 0)+
          sSup (Set.range (fun x : ℝ => ‖iteratedDeriv i.val E x‖)) := by
    by_cases hi : i=0
    · subst i
      simpa using hzero
    · have hpos : 0 < i.val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hi)
      have hd : iteratedDeriv i.val (fun u => c+E u) = iteratedDeriv i.val E :=
        funext fun x => iteratedDeriv_const_add hpos c
      rw [hd,if_neg hi,zero_add]
  calc
    periodicCjNorm j (fun x => c+E x) ≤
        ∑ i : Fin (j+1), ((if i=0 then ‖c‖ else 0)+
          sSup (Set.range (fun x : ℝ => ‖iteratedDeriv i.val E x‖))) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = ‖c‖+periodicCjNorm j E := by
      simp [periodicCjNorm,Finset.sum_add_distrib]

end Lemniscate
