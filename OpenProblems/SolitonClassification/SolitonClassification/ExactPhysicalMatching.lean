import SolitonClassification.PhysicalSectionInjective
import SolitonClassification.ReflectedGeometry

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open ReflectedArc

theorem translated_solution (d : ℝ) (x : Phase) (p s : ℝ) :
    solution d x (s+p) = solution d (solution d x p) s := by
  let f := fun r : ℝ => solution d x (r+p)
  have start : f 0=solution d x p := by simp [f]
  have rates (u : ℝ) : HasDerivAt f (rhs d (f u)) u := by
    have dt : HasDerivAt (fun r : ℝ => r+p) 1 u := (hasDerivAt_id u).add_const p
    simpa [f,Function.comp_def] using (solution_derivative d x (u+p)).scomp u dt
  have eq := (exists_unique_solution d (solution d x p)).unique ⟨start,rates⟩
    ⟨solution_zero _ _,solution_derivative _ _⟩
  exact congrFun eq s

/-- Once the four matching coordinates agree at positive physical radius,
    uniqueness propagates the coincidence to the seam itself. Reflection
    then yields the actual smooth periodic immersion with zero total turn. -/
theorem exact_physical_matching {b s t : ℝ} {Y : Phase} (hs : 0<s) (ht : t<0)
    (v0 : Y 1=0) (q0 : Y 3=0) :
    let x := solution 1 ![0,b,0,0] s
    let y := solution 1 Y t
    regular x → regular y → 4 ≤ root x/scale x → 4 ≤ root y/scale y →
    0 ≤ along x → 0 ≤ along y → scale x=scale y → shape x=shape y → slope x=slope y →
    root x/scale x*across x=root y/scale y*across y → height x=height y →
    Nonempty (ZeroTurnExpander (4*(s-t)) b) := by
  intro x y rx ry bx by' ax ay radius U w I H
  have same := physical_state_injective rx ry bx by' ax ay radius U w I H
  dsimp only [x,y] at same
  have hit : solution 1 ![0,b,0,0] (s-t) = Y := by
    calc
      _ = solution 1 (solution 1 ![0,b,0,0] s) (-t) := by
        rw [show s-t = -t+s by ring,translated_solution]
      _ = solution 1 (solution 1 Y t) (-t) := by rw [same]
      _ = Y := by rw [←translated_solution,neg_add_cancel,solution_zero]
  apply exists_zeroTurnExpander_of_quarter (z := solution 1 ![0,b,0,0]) (by linarith)
  · exact continuous_iff_continuousAt.mpr fun r => (solution_derivative _ _ r).continuousAt
  · exact fun r _ => solution_derivative _ _ r
  · exact solution_zero _ _
  · rw [hit]; exact v0
  · rw [hit]; exact q0

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.exact_physical_matching
