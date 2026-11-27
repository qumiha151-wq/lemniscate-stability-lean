import SolitonClassification.Rotating.IntegerHullFromTapes
import SolitonClassification.Rotating.ResetOnlyCells

namespace SolitonClassification.Rotating.IntegerTarget
open DyadicReset
noncomputable section

private theorem endpoints {n : ℤ} {grid : ℕ → Node} (row : ℕ → TapeRow n)
    (indices : ∀ i : ℕ, i<4000 → (row i).left=grid i ∧ (row i).right=grid (i+1)) :
    ∃ T : PolynomialTape n 4000, T.node 0=grid 0 ∧
      ∀ j : ℕ, (T.data 3999 j).sum=((grid 4000)[j]?).getD 0 := by
  have joins (i : ℕ) (h : i+1<4000) : (row i).right=(row (i+1)).left :=
    (indices i (by omega)).2.trans (indices (i+1) h).1.symm
  refine ⟨assemble row joins,(indices 0 (by decide)).1,?_⟩
  intro j
  change ((packedData (row 3999).input) j).sum=_
  rw [packed_sum,(row 3999).endpoints.2,(indices 3999 (by decide)).2]

theorem square_immersion_from_indexed_rows
    (P : ℕ → TapeRow Middle.hn) (M : ℕ → TapeRow (-Middle.hn))
    (hiP : ∀ i : ℕ, i<4000 → (P i).left=GridPlus.atNode i ∧ (P i).right=GridPlus.atNode (i+1))
    (hiM : ∀ i : ℕ, i<4000 → (M i).left=GridMinus.atNode i ∧ (M i).right=GridMinus.atNode (i+1)) :
    ∃c∈cube, ∃I : WindingOneImmersion (c 4) (2*c 2),
      60<2*c 2 ∧ 2*c 2<62 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<I.k 0 ∧
      (∃s, I.k s<0) ∧ c 4*(I.x 0*deriv I.x 0+I.y 0*deriv I.y 0)≠0 ∧
      IsLeast {h : ℝ | 0<h ∧ Function.Periodic I.x h ∧ Function.Periodic I.y h} (2*c 2) ∧
      (∀w : ℝ × ℝ, |w.1|≤1/20 → |w.2|≤1/20 → w∈convexHull ℝ (Set.range (fun s => (I.x s,I.y s)))) := by
  obtain ⟨p,hp,sp⟩ := endpoints P hiP
  obtain ⟨m,hm,sm⟩ := endpoints M hiM
  obtain ⟨pi,mi,pe,me⟩ := actual_grid_ends
  exact primitive_square_of_certified_tapes p m (hp.trans pi) (hm.trans mi)
    (fun j => by rw [sp j,pe]) (fun j => by rw [sm j,me])

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.square_immersion_from_indexed_rows
