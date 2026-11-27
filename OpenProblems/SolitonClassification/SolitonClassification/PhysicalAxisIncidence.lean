import SolitonClassification.PhysicalQuarterSymmetry

noncomputable section
open Set
namespace ClosedSimilarity.CrossingFrame
open ReflectedArc CrossingResponse

/-- The signed axial and transverse fast velocities yield a pair of actual
nonparallel position derivatives at a point of the physical seam ray. Both
signs of that position are fixed by reflection across the seam. -/
theorem incidence_of_lab_root {b S β s : ℝ} (P : ZeroTurnExpander (4*S) b)
    (pb : 0<b) (sp : 0<S) (hv : P.cartesianSupport S 1=0) (hq : P.cartesianSupport S 3=0)
    (seamPos : 0<Y ((b^2)⁻¹) (Real.sqrt b*S))
    (seam : X ((b^2)⁻¹) (Real.sqrt b*S)=β*Y ((b^2)⁻¹) (Real.sqrt b*S))
    (root : labX b s=β*labY b s)
    (inc : (Real.cos (turn b s)-β*Real.sin (turn b s))*
      (Real.sin (turn b s)+β*Real.cos (turn b s))≠0) :
    let g : ℝ → ℝ × ℝ := fun t => (P.X t,P.Y t)
    (∀ t, g (2*S-t)=g s ↔ g t=g s) ∧ (∀ t, g (2*S-t)= -g s ↔ g t= -g s) ∧
      ∃ u∈Ico (0:ℝ) (4*S), ∃ v∈Ico (0:ℝ) (4*S), u≠v ∧ g u=g s ∧ g v=g s ∧
        deriv P.X u*deriv P.Y v-deriv P.Y u*deriv P.X v≠0 := by
  have dp := Real.sqrt_pos.mpr pb
  have ss : labX b S=β*labY b S := by
    change X ((b^2)⁻¹) (Real.sqrt b*S)/Real.sqrt b=β*(Y ((b^2)⁻¹) (Real.sqrt b*S)/Real.sqrt b)
    rw [seam]; ring
  have sn : labY b S ≠ 0 := (div_pos seamPos dp).ne'
  have on := on_seam_axis_of_lab P pb hq ss sn root
  refine ⟨?_,?_,?_⟩
  · intro t
    simpa only [Prod.mk.injEq,one_mul] using reflected_hit_iff P pb hv hq on 1 t
  · intro t
    simpa only [Prod.neg_mk,Prod.mk.injEq,neg_one_mul] using reflected_hit_iff P pb hv hq on (-1) t
  · obtain ⟨u,hu,v,hv',ne,ux,uy,vx,vy,det⟩ := transverse_in_every_physical_period P
      pb hv hq ss sn root inc (show 0<4*S by positivity) P.closed_X P.closed_Y
    exact ⟨u,hu,v,hv',ne,Prod.ext ux uy,Prod.ext vx vy,det⟩

end ClosedSimilarity.CrossingFrame
#print axioms ClosedSimilarity.CrossingFrame.incidence_of_lab_root
