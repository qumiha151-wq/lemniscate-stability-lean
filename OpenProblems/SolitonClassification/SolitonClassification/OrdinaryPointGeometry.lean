import SolitonClassification.QuarterReflectionLabels
import SolitonClassification.PhysicalCrossingFrame

noncomputable section
open Set
namespace ClosedSimilarity.CrossingFrame

/-- In one traversal exactly two distinct labels attain this position, and
the two Cartesian derivative vectors there have nonzero determinant. -/
def OrdinaryTransversePoint (X Y : ℝ → ℝ) (L : ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ a ∈ Ico (0:ℝ) L, ∃ b ∈ Ico (0:ℝ) L, a < b ∧
    (∀ t ∈ Ico (0:ℝ) L, (X t,Y t)=p ↔ t=a ∨ t=b) ∧
    deriv X a*deriv Y b-deriv Y a*deriv X b≠0

/-- If the two labels are known, transversality may be checked on any
ordered pair of preimages of the same point in this traversal. -/
theorem ordinary_of_labels (X Y : ℝ → ℝ) {S r : ℝ} {p : ℝ × ℝ} (inside : r∈Ioo 0 S)
    (labels : ∀ t∈Ico (0:ℝ) (4*S), (X t,Y t)=p ↔ t=r ∨ t=2*S-r)
    (transverse : ∃ u∈Ico (0:ℝ) (4*S), ∃ v∈Ico (0:ℝ) (4*S),
      u≠v ∧ (X u,Y u)=p ∧ (X v,Y v)=p ∧
      deriv X u*deriv Y v-deriv Y u*deriv X v≠0) :
    OrdinaryTransversePoint X Y (4*S) p := by
  obtain ⟨lo,hi⟩ := inside
  refine ⟨r,⟨lo.le,by linarith⟩,2*S-r,⟨by linarith,by linarith⟩,by linarith,labels,?_⟩
  obtain ⟨u,hu,v,hv,ne,pu,pv,det⟩ := transverse
  obtain ur | ur := (labels u hu).1 pu <;> obtain vr | vr := (labels v hv).1 pv
  · exact (ne (ur.trans vr.symm)).elim
  · rwa [ur,vr] at det
  · rw [ur,vr] at det
    intro zero
    apply det
    linear_combination -zero
  · exact (ne (ur.trans vr.symm)).elim

end ClosedSimilarity.CrossingFrame
#print axioms ClosedSimilarity.CrossingFrame.ordinary_of_labels
