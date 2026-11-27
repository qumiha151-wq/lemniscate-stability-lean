import SolitonClassification.FourthOrderDisconjugacy
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card

noncomputable section
open Set
namespace SolitonClassification.CrossingMultiplicity

/-- A local disconjugacy statement gives an actual finite zero set; in
    particular an infinite zero set cannot be lost by natural cardinality. -/
theorem finite_zero_set_of_not_four_zeros {f : ℝ → ℝ} {a b : ℝ} (no : ¬ FourZeros f a b) :
    {x ∈ Icc a b | f x = 0}.Finite ∧ {x ∈ Icc a b | f x = 0}.ncard ≤ 3 := by
  let S := {x ∈ Icc a b | f x = 0}
  have impossible (F : Finset ℝ) (sub : (F : Set ℝ) ⊆ S) (card : F.card = 4) : False := by
    let x := F.orderEmbOfFin card
    have ok (i : Fin 4) : x i ∈ S := sub (F.orderEmbOfFin_mem card i)
    exact no ⟨x 0,x 1,x 2,x 3,(ok 0).1.1,x.strictMono (by decide : (0 : Fin 4) < 1),
          x.strictMono (by decide : (1 : Fin 4) < 2),x.strictMono (by decide : (2 : Fin 4) < 3),
          (ok 3).1.2,(ok 0).2,(ok 1).2,(ok 2).2,(ok 3).2⟩
  have finite : S.Finite := by
    by_contra inf
    obtain ⟨F,sub,card⟩ := Set.Infinite.exists_subset_card_eq inf 4
    exact impossible F sub card
  refine ⟨finite,?_⟩
  change S.ncard ≤ 3
  rw [Set.ncard_eq_toFinset_card _ finite]
  by_contra! large
  obtain ⟨F,sub,card⟩ := Finset.exists_subset_card_eq (show 4 ≤ finite.toFinset.card by omega)
  apply impossible F _ card
  exact fun _ hx => finite.mem_toFinset.mp (sub hx)

end SolitonClassification.CrossingMultiplicity
#print axioms SolitonClassification.CrossingMultiplicity.finite_zero_set_of_not_four_zeros
