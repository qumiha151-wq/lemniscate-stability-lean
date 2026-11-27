import SolitonClassification.Rotating.ResetGridClosure
import SolitonClassification.Rotating.ResetAllInversesMinus
import SolitonClassification.Rotating.ResetAllInversesPlus

namespace SolitonClassification.Rotating.IntegerTarget
open DyadicReset
noncomputable section

/-- All remaining checks are on the polynomial coefficients of one cell. -/
def CellTests (n : ℤ) (grid : ℕ→Node) (cells : Fin 4000 → PackedCell) : Prop :=
  ∀ i, SignedCheck n (packedData (cells i)) ∧ Small (packedData (cells i)) ∧
    sampleStart (cells i)=grid i.val ∧ sampleEnd (cells i)=grid (i.val+1)

private theorem make_rows {n : ℤ} {grid : ℕ→Node} {c : Fin 4000→PackedCell}
    (hc : CellTests n grid c) (inv : ∀i : ℕ, i≤4000 → ∃w, CheckedNode (grid i) w) :
    ∃ row : ℕ→TapeRow n, ∀i : ℕ, i<4000 → (row i).left=grid i ∧ (row i).right=grid (i+1) := by
  classical
  let mk (i : Fin 4000) : TapeRow n :=
    ⟨c i, grid i.val,grid (i.val+1),Classical.choose (inv i.val i.isLt.le),
      (hc i).1,(hc i).2.1,(hc i).2.2,Classical.choose_spec (inv i.val i.isLt.le)⟩
  refine ⟨fun i => mk ⟨i%4000,Nat.mod_lt _ (by decide)⟩,?_⟩
  intro i hi
  change grid (i%4000)=grid i ∧ grid (i%4000+1)=grid (i+1)
  simp only [Nat.mod_eq_of_lt hi, and_self]

theorem immersion_from_polynomial_cells
    (P M : Fin 4000→PackedCell) (hp : CellTests Middle.hn GridPlus.atNode P)
    (hm : CellTests (-Middle.hn) GridMinus.atNode M) :
    ∃c∈cube, ∃I : WindingOneImmersion (c 4) (2*c 2),
      60<2*c 2 ∧ 2*c 2<62 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<I.k 0 ∧
      (∃s, I.k s<0) ∧ c 4*(I.x 0*deriv I.x 0+I.y 0*deriv I.y 0)≠0 := by
  obtain ⟨p,pr⟩ := make_rows hp AllInversesPlus.every_node
  obtain ⟨m,mr⟩ := make_rows hm AllInversesMinus.every_node
  exact immersion_from_indexed_rows p m pr mr

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.immersion_from_polynomial_cells
