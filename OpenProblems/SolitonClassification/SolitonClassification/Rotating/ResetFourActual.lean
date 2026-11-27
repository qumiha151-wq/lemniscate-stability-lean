import SolitonClassification.Rotating.ResetLift
import SolitonClassification.Rotating.ResetShadow
import SolitonClassification.Rotating.ResetCell1999
import SolitonClassification.Rotating.ResetCell2000
import SolitonClassification.Rotating.ResetCell2001
import SolitonClassification.Rotating.ResetCell2002
noncomputable section
open Set
namespace SolitonClassification.Rotating.DyadicReset.Block2000
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem table_link {A B : Array (List ℤ)} {a b : Array ℤ}
    (l : A.map List.sum=a) (r : B.map (fun p => p.head?.getD 0)=b) (eq : a=b) (i : Nat) :
    ((A[i]?).getD []).sum=(((B[i]?).getD []).head?.getD 0) := by
  have e := congrArg (fun z : Array ℤ => (z[i]?).getD 0) (l.trans (eq.trans r.symm))
  simp only [Array.getElem?_map] at e
  cases h : A[i]? <;> cases k : B[i]? <;> simp [h,k] at * <;> assumption

private theorem lift_link {p q : Data} (m : ∀i,(p i).sum=((q i).head?.getD 0)) :
    lift p 1=lift q 0 := by
  obtain ⟨sx,cols⟩ := adjacent_matching m
  apply Prod.ext sx
  funext j;change weightFactor • column _ _ j 1=weightFactor • column _ _ j 0
  rw [cols j]

theorem small1999 : Small Cell1999.table := by unfold Small; decide +kernel
theorem small2000 : Small Cell2000.table := by unfold Small; decide +kernel
theorem small2001 : Small Cell2001.table := by unfold Small; decide +kernel
theorem small2002 : Small Cell2002.table := by unfold Small; decide +kernel
theorem join1999 : lift Cell1999.table 1=lift Cell2000.table 0 := by
  apply lift_link
  exact table_link Cell1999.matching.2 Cell2000.matching.1 (by decide +kernel)
theorem join2000 : lift Cell2000.table 1=lift Cell2001.table 0 := by
  apply lift_link
  exact table_link Cell2000.matching.2 Cell2001.matching.1 (by decide +kernel)
theorem join2001 : lift Cell2001.table 1=lift Cell2002.table 0 := by
  apply lift_link
  exact table_link Cell2001.matching.2 Cell2002.matching.1 (by decide +kernel)

def Follows (x : ℝ→Aug) := ∀t∈Icc 0 1,HasDerivWithinAt x (h • augmented (x t)) (Icc 0 1) t
def Close (x : ℝ→Aug) (p : Data) (c : ℝ) := ∀t∈Icc 0 1,‖x t-lift p t‖≤c*eps

theorem solve {p : Data} (ce : Certified p) (sm : Small p) (a : Aug) {δ : ℝ}
    (small : δ*eps≤1/4) (near : ‖a-lift p 0‖≤δ*eps) :
    ∃ x : ℝ→Aug, x 0=a ∧ Follows x ∧ Close x p (3*δ+2) := by
  obtain ⟨x,ini,xd,err⟩ := shadow_cell (lift_deriv p) (liftVelocity_cont p)
    (fun t ht => ⟨lift_inner sm ht,lift_residual ce ht⟩) (a-lift p 0) (near.trans small)
  refine ⟨x,by simpa using ini,xd,?_⟩
  intro t ht
  have q := err t ht
  linarith only [q,near]

/-- One actual solution across four adjacent cells. Its state and its five
linearized columns are never restarted; exact values match at the joins.
The columns use the fixed factor 1/16384 in the product norm. -/
theorem four_cells : ∃x₀ x₁ x₂ x₃ : ℝ→Aug,
    x₀ 0=lift Cell1999.table 0 ∧ x₁ 0=x₀ 1 ∧ x₂ 0=x₁ 1 ∧ x₃ 0=x₂ 1 ∧
    Follows x₀ ∧ Follows x₁ ∧ Follows x₂ ∧ Follows x₃ ∧
    Close x₀ Cell1999.table 2 ∧ Close x₁ Cell2000.table 8 ∧
    Close x₂ Cell2001.table 26 ∧ Close x₃ Cell2002.table 80 := by
  obtain ⟨x₀,h₀,d₀,e₀⟩ := solve (δ:=0) ⟨Cell1999.checked⟩ small1999 (lift Cell1999.table 0)
    (by norm_num [eps]) (by norm_num)
  norm_num only [mul_zero,zero_add] at e₀
  have n₁ := e₀ 1 (by norm_num : (1:ℝ)∈Icc 0 1)
  rw [join1999] at n₁
  obtain ⟨x₁,h₁,d₁,e₁⟩ := solve (δ:=2) ⟨Cell2000.checked⟩ small2000 (x₀ 1)
    (by norm_num [eps]) n₁
  norm_num only [Nat.reduceMul] at e₁
  have n₂ := e₁ 1 (by norm_num : (1:ℝ)∈Icc 0 1)
  rw [join2000] at n₂
  obtain ⟨x₂,h₂,d₂,e₂⟩ := solve (δ:=8) ⟨Cell2001.checked⟩ small2001 (x₁ 1)
    (by norm_num [eps]) (by convert! n₂ using 1)
  have n₃ := e₂ 1 (by norm_num : (1:ℝ)∈Icc 0 1)
  rw [join2001] at n₃
  obtain ⟨x₃,h₃,d₃,e₃⟩ := solve (δ:=26) ⟨Cell2002.checked⟩ small2002 (x₂ 1)
    (by norm_num [eps]) (by convert! n₃ using 1; norm_num)
  refine ⟨x₀,x₁,x₂,x₃,h₀,h₁,h₂,h₃,d₀,d₁,d₂,d₃,e₀,?_,?_,?_⟩
  · convert! e₁ using 1
  · convert! e₂ using 1; norm_num
  · convert! e₃ using 1; norm_num
end SolitonClassification.Rotating.DyadicReset.Block2000
#print axioms SolitonClassification.Rotating.DyadicReset.Block2000.four_cells
