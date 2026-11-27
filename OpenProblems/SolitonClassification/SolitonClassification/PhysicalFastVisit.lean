import SolitonClassification.PhysicalQuarterSymmetry
import SolitonClassification.MatchedAxisVisits

noncomputable section
open Set
namespace ClosedSimilarity.CrossingFrame
open CrossingResponse ReflectedArc

/-- Exact Cartesian position at an arbitrary fast label, in the original
axes of the smooth profile. Its initial unit tangent is the rotation. -/
theorem position_at_fast_label {L b : ℝ} (P : ZeroTurnExpander L b) (pb : 0<b) (r : ℝ) :
    let e := (b^2)⁻¹
    let A := deriv P.X 0
    let B := deriv P.Y 0
    P.X (r/Real.sqrt b)=(A*X e r-B*Y e r)/Real.sqrt b ∧
    P.Y (r/Real.sqrt b)=(A*Y e r+B*X e r)/Real.sqrt b := by
  obtain ⟨hx,hy⟩ := (physical_position P pb).2 (r/Real.sqrt b)
  have clock : time b (r/Real.sqrt b)=r := by unfold time; field_simp [(Real.sqrt_pos.mpr pb).ne']
  simp only [labX,labY,clock,rate] at hx hy
  dsimp only
  constructor
  · rw [hx]; ring
  · rw [hy]; ring

/-- The same scalar tests signed incidence in physical and fast coordinates.
This includes genuine coincidence and central inversion. -/
theorem physical_fast_signed_iff {L b : ℝ} (P : ZeroTurnExpander L b) (pb : 0<b) (t r κ : ℝ) :
    (P.X (t/Real.sqrt b)=κ*P.X (r/Real.sqrt b) ∧
     P.Y (t/Real.sqrt b)=κ*P.Y (r/Real.sqrt b)) ↔
    (X ((b^2)⁻¹) t=κ*X ((b^2)⁻¹) r ∧ Y ((b^2)⁻¹) t=κ*Y ((b^2)⁻¹) r) := by
  have clock (s : ℝ) : time b (s/Real.sqrt b)=s := by
    unfold time; field_simp [(Real.sqrt_pos.mpr pb).ne']
  simpa only [clock,rate] using physical_fast_scalar_iff P pb (t/Real.sqrt b) (r/Real.sqrt b) κ

end ClosedSimilarity.CrossingFrame

namespace ClosedSimilarity.CrossingResponse.QuarterVisits
open CrossingFrame ReflectedArc
variable {L b S β : ℝ} {N : ℕ} (q : QuarterVisits b S β N)

def physicalTime (i : Fin N) := q.time i/Real.sqrt b

/-- The selected label lies strictly inside the first quarter. Its original
positive axis height and both its incidence inequalities survive the conversion. -/
theorem physical_incidence (pb : 0<b) (i : Fin N) :
    q.physicalTime i∈Ioo 0 S ∧ 0<labY b (q.physicalTime i) ∧
    labX b (q.physicalTime i)=β*labY b (q.physicalTime i) ∧
    (Real.cos (turn b (q.physicalTime i))-β*Real.sin (turn b (q.physicalTime i)))*
      (Real.sin (turn b (q.physicalTime i))+β*Real.cos (turn b (q.physicalTime i)))≠0 := by
  obtain ⟨inside,pos,onAxis,vx,vy,_⟩ := q.visit i
  have g := Real.sqrt_pos.mpr pb
  have clock : CrossingFrame.time b (q.physicalTime i)=q.time i := by
    unfold CrossingFrame.time physicalTime; field_simp [g.ne']
  refine ⟨⟨div_pos inside.1 g,(div_lt_iff₀ g).mpr (by linarith [inside.2])⟩,?_,?_,?_⟩
  · simp only [labY,clock,rate]; exact div_pos pos g
  · simp only [labX,labY,clock,rate]; rw [onAxis,mul_div_assoc]
  · simp only [turn,clock,rate]
    exact mul_ne_zero vx (by simpa only [add_comm,tx,ty] using vy)

/-- Across the full first physical quarter each selected image has exactly
one preimage and its antipode has none. -/
theorem physical_first_quarter (P : ZeroTurnExpander L b) (pb : 0<b) (i : Fin N)
    (t : ℝ) (ht : t∈Icc (0:ℝ) S) :
    (P.X t=P.X (q.physicalTime i) → P.Y t=P.Y (q.physicalTime i) → t=q.physicalTime i) ∧
      ¬(P.X t= -P.X (q.physicalTime i) ∧ P.Y t= -P.Y (q.physicalTime i)) := by
  have g := Real.sqrt_pos.mpr pb
  have bt : Real.sqrt b*t∈Icc (0:ℝ) (Real.sqrt b*S) :=
    ⟨mul_nonneg g.le ht.1,mul_le_mul_of_nonneg_left ht.2 g.le⟩
  have test := (q.visit i).2.2.2.2.2 (Real.sqrt b*t) bt
  have phys (κ : ℝ) := physical_fast_signed_iff P pb (Real.sqrt b*t) (q.time i) κ
  have cancel : Real.sqrt b*t/Real.sqrt b=t := by field_simp [g.ne']
  constructor
  · intro hx hy
    have fast := (phys 1).mp (by simpa only [physicalTime,cancel,one_mul] using And.intro hx hy)
    simp only [one_mul] at fast
    exact (eq_div_iff g.ne').mpr (by linarith only [test.1 fast.1 fast.2])
  · intro opposite
    have fast := (phys (-1)).mp (by simpa only [physicalTime,cancel,neg_one_mul] using opposite)
    exact test.2 (by simpa only [neg_one_mul] using fast)

/-- Pair-valued formulation for the global reflection label theorem. -/
theorem physical_first_quarter_pair (P : ZeroTurnExpander L b) (pb : 0<b) (i : Fin N) :
    let g := fun t => (P.X t,P.Y t)
    let p := g (q.physicalTime i)
    (∀t∈Icc (0:ℝ) S, g t=p → t=q.physicalTime i) ∧
    (∀t∈Icc (0:ℝ) S, g t≠ -p) := by
  constructor
  · intro t ht eq
    exact (q.physical_first_quarter P pb i t ht).1 (congrArg Prod.fst eq) (congrArg Prod.snd eq)
  · intro t ht eq
    exact (q.physical_first_quarter P pb i t ht).2 ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩

/-- Distinct chosen heights give distinct physical plane points, including
for a profile whose initial tangent is arbitrarily rotated. -/
theorem injective_physical_image (P : ZeroTurnExpander L b) (pb : 0<b) :
    Function.Injective (fun i => (P.X (q.physicalTime i),P.Y (q.physicalTime i))) := by
  intro i j eq
  obtain ⟨hx,hy⟩ := Prod.mk.inj eq
  have h := (physical_fast_signed_iff P pb (q.time i) (q.time j) 1).mp
    (by simpa only [physicalTime,one_mul] using And.intro hx hy)
  exact q.distinct (by simpa only [one_mul] using h.2)

end ClosedSimilarity.CrossingResponse.QuarterVisits
#print axioms ClosedSimilarity.CrossingFrame.physical_fast_signed_iff
#print axioms ClosedSimilarity.CrossingResponse.QuarterVisits.physical_incidence
#print axioms ClosedSimilarity.CrossingResponse.QuarterVisits.physical_first_quarter
#print axioms ClosedSimilarity.CrossingResponse.QuarterVisits.injective_physical_image


