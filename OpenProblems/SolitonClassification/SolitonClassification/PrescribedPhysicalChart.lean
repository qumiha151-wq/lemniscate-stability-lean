import SolitonClassification.PrescribedSeamSections
import SolitonClassification.PrescribedIncomingSector

noncomputable section
open Set
namespace ClosedSimilarity.GlobalSupport.MovingSeam

def PrescribedSection.normalizedState {a b H E : ℝ} (w : PrescribedSection a b H E)
    (z : Icc a b × Icc (0:ℝ) E) : Phase := shot (w.drive z) z.1 (-w.flight z)

/-- A single physical shot realizes all the chart coordinates at the same
    negative arclength and at the requested physical inverse radius. -/
theorem PrescribedSection.physical_chart {a b H E : ℝ} (w : PrescribedSection a b H E)
    (z : Icc a b × Icc (0:ℝ) E) (ePos : 0<(z.2:ℝ)) :
    ∃ l>0, l^4*w.drive z=1 ∧
      let Y := restore l ![(z.1:ℝ),0,1,0]
      let t := -w.flight z/l
      let y := solution 1 Y t
      let x := w.normalizedState z
      t<0 ∧ Y 1=0 ∧ Y 3=0 ∧ regular y ∧ ReflectedArc.RadialLayer.eps (solution 1 Y) t=z.2 ∧
        -height y=H ∧ impact y=impact x ∧ along y=along x ∧
        root y/scale y=root x/scale x ∧ shape y=shape x ∧ slope y=slope x := by
  obtain ⟨l,hl,eq,eps,h,i⟩ := w.physical z ePos
  refine ⟨l,hl,eq,?_⟩
  let Y := restore l ![(z.1:ℝ),0,1,0]
  let t := -w.flight z/l
  let y := solution 1 Y t
  let x := w.normalizedState z
  change t<0 ∧ Y 1=0 ∧ Y 3=0 ∧ regular y ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  have tm : l*t= -w.flight z := by dsimp [t]; field_simp
  have state : y = restore l x := by
    change solution 1 (restore l ![(z.1:ℝ),0,1,0]) t=_
    rw [physical_support_conjugacy eq,tm]
    rfl
  obtain ⟨ss,rt,sh,sl,al,_,_,_⟩ := restore_invariants hl x
  have rg := w.regular_incoming z
  have rx : regular (restore l x) := by
    have r : radiusSquared (restore l x)=l^6*radiusSquared x := by simp [radiusSquared,restore]; ring
    have s : stressSquared (restore l x)=l^4*stressSquared x := by simp [stressSquared,restore]; ring
    exact ⟨r ▸ mul_pos (pow_pos hl _) rg.1,s ▸ mul_pos (pow_pos hl _) rg.2⟩
  refine ⟨div_neg_of_neg_of_pos (by linarith [w.late z]) hl,by simp [Y,restore],by simp [Y,restore],
    state ▸ rx,eps,h,i,?_,?_,?_,?_⟩
  · change along y=along x; rw [state,al]
  · change root y/scale y=root x/scale x
    rw [state,rt,ss,mul_div_mul_left _ _ hl.ne']
  · change shape y=shape x; rw [state,sh]
  · change slope y=slope x; rw [state,sl]

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.PrescribedSection.physical_chart
