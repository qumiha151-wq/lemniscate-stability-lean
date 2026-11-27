import SolitonClassification.PhysicalFastVisit
import SolitonClassification.PhysicalAxisIncidence
import SolitonClassification.OrdinaryPointGeometry

noncomputable section
open Set
namespace ClosedSimilarity.CrossingFrame
open GlobalSupport.MovingSeam ReflectedArc CrossingResponse

/-- For every desired number of ordinary transverse double points and
every lower bound on the centre marker, there is a smooth closed normalized
homothetic elastic expander of total turning zero that exceeds the marker
bound and has that many distinct ordinary transverse double points. Its
stated period is the least positive period of its actual position. -/
theorem unbounded_primitive_ordinary_crossings (N : ℕ) (A : ℝ) :
    ∃ b>A, 0<b ∧ ∃ L>0, ∃ P : ZeroTurnExpander L b,
      IsLeast {d : ℝ | 0<d ∧ Function.Periodic (fun t => (P.X t,P.Y t)) d} L ∧
      ∃ points : Fin N → ℝ × ℝ, Function.Injective points ∧
        ∀ i, OrdinaryTransversePoint P.X P.Y L (points i) := by
  obtain ⟨b,high,pb,S,sp,P,β,hv,hq,sy,seam,⟨q⟩⟩ := exists_matched_axis_visits (N+1) A
  let g : ℝ → ℝ × ℝ := fun t => (P.X t,P.Y t)
  have per : Function.Periodic g (4*S) := fun t => Prod.ext (P.closed_X t) (P.closed_Y t)
  have odd (t : ℝ) : g (-t)= -g t := physical_odd P pb t
  have at_point (i : Fin (N+1)) :
      IsLeast {d : ℝ | 0<d ∧ Function.Periodic g d} (4*S) ∧
      OrdinaryTransversePoint P.X P.Y (4*S) (g (q.physicalTime i)) := by
    obtain ⟨inside,_,root,vel⟩ := q.physical_incidence pb i
    obtain ⟨plus,minus,cross⟩ := incidence_of_lab_root P pb sp hv hq sy seam root vel
    obtain ⟨one,opposite⟩ := q.physical_first_quarter_pair P pb i
    have labels := QuarterReflection.exact_labels per odd plus minus inside rfl one opposite
    exact ⟨QuarterReflection.least_period_of_labels per inside labels,
      ordinary_of_labels P.X P.Y inside labels cross⟩
  refine ⟨b,high,pb,4*S,by positivity,P,(at_point 0).1,
    fun i => g (q.physicalTime i.castSucc),?_,fun i => (at_point i.castSucc).2⟩
  exact (q.injective_physical_image P pb).comp (Fin.castSucc_injective N)

end ClosedSimilarity.CrossingFrame
#print axioms ClosedSimilarity.CrossingFrame.unbounded_primitive_ordinary_crossings
