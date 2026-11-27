import LengthGrowth.ActualFlow.MaterialTurnPrimitives
import Mathlib.Data.Finset.Sort

noncomputable section
open Set Finset MeasureTheory
namespace LengthGrowth.ActualFlow.PeriodicRegularPosition

/-- Ordered material labels realizing the quarter-radian excursions
    extracted from a low-dissipation record. -/
theorem material_labels_of_excursions (p : PeriodicRegularPosition) {m : ℕ}
    (h : p.HasTurningExcursions m) : ∃ l r : Fin m→ℝ,
    (∀i,l i≤r i) ∧ (∀i j,i<j → r i≤l j) ∧ (∀i j,r i≤l j+p.period) ∧
    ∀i,1/4≤|arcTurn p.position (l i) (r i)| := by
  classical
  let P := Real.sqrt (2*(materialEnergy p.position p.period*p.length))
  have hp : 0<P := Real.sqrt_pos.mpr (by positivity [p.material_energy_pos,p.length_pos])
  let c := p.length/P
  have cp : 0<c := div_pos p.length_pos hp
  have span : c*P=p.length := div_mul_cancel₀ _ hp.ne'
  obtain ⟨a,U,card,ok,disj⟩ := h
  have sep {I J : ℝ×ℝ} (hi : I∈U) (hj : J∈U) (diff : I≠J) (lt : I.1≤J.1) : I.2≤J.1 := by
    by_contra! bad
    let z := (J.1+min I.2 J.2)/2
    have lo : J.1<min I.2 J.2 := lt_min bad (ok J hj).2.1
    have lb : J.1<z := by dsimp [z]; linarith
    have ub : z<min I.2 J.2 := by dsimp [z]; linarith
    exact Set.disjoint_left.mp (disj I hi J hj diff)
      (show z∈Ioo I.1 I.2 from ⟨lt.trans_lt lb,ub.trans_le (min_le_left ..)⟩)
      ⟨lb,ub.trans_le (min_le_right ..)⟩
  have inju : (↑U : Set (ℝ×ℝ)).InjOn Prod.fst := by
    intro I hi J hj eq
    by_contra diff
    have H := sep hi hj diff eq.le
    linarith [show I.1=J.1 from eq,(ok I hi).2.1]
  let lefts := U.image Prod.fst
  have size : lefts.card=m := (card_image_of_injOn inju).trans card
  let xs := lefts.orderIsoOfFin size
  have labels (i : Fin m) : ∃ I∈U, I.1=(xs i:ℝ) := Finset.mem_image.mp (xs i).property
  choose q valid equal using labels
  let ax := fun u => p.arclengthInverse (c*u)
  have mono : StrictMono ax := p.arclengthOrderIso.symm.strictMono.comp (strictMono_id.const_mul cp)
  refine ⟨fun i => ax (q i).1,fun i => ax (q i).2,fun i => (mono (ok _ (valid i)).2.1).le,?_,?_,?_⟩
  · intro i j hij
    have less : (q i).1<(q j).1 := by rw [equal i,equal j]; exact xs.strictMono hij
    exact mono.monotone (sep (valid i) (valid j) (fun same => less.ne (congrArg Prod.fst same)) less.le)
  · intro i j
    have bd : (q i).2≤(q j).1+P := by linarith only [(ok _ (valid i)).2.2.1,(ok _ (valid j)).1]
    have hit := mono.monotone bd
    simpa only [ax,mul_add,span,p.inverse_add_length] using hit
  · intro i
    change 1/4≤|arcTurn p.position (p.arclengthInverse (c*_)) (p.arclengthInverse (c* _))|
    rw [← p.arcTurn_scaled]
    exact (ok _ (valid i)).2.2.2

end LengthGrowth.ActualFlow.PeriodicRegularPosition
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.material_labels_of_excursions
