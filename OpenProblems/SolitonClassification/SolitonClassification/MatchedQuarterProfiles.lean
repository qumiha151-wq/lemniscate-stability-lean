import SolitonClassification.MatchedCrossingSequence
import SolitonClassification.StrongCentreMarker

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam.MatchedSequence
open ReflectedArc
variable {H E B : ℝ} {c : CentreChart H E B} {w : WindingChart H E} {f : w.Flight}
variable (m : MatchedSequence c w f)

def quarter (i : ℕ) : ℝ := c.time (m.marker i) + f.length (m.seamParameter i)

theorem marker_pos (big : 32 ≤ B) (i : ℕ) : 0 < (m.marker i : ℝ) :=
  (show (0:ℝ)<32 by norm_num).trans_le (big.trans (m.marker i).property)

theorem positive_quarter (i : ℕ) : 0 < m.quarter i := m.seam_positive i

theorem profiles (i : ℕ) : Nonempty (ZeroTurnExpander (4*m.quarter i) (m.marker i)) := by
  apply exists_zeroTurnExpander_of_quarter (z := solution 1 ![0,(m.marker i:ℝ),0,0])
    (m.seam_positive i)
  · exact continuous_iff_continuousAt.mpr fun r => (solution_derivative _ _ r).continuousAt
  · exact fun r _ => solution_derivative _ _ r
  · exact solution_zero _ _
  · exact (m.reflection i).1
  · exact (m.reflection i).2

theorem fast_seams_diverge (big : 32≤B) (a : c.FirstIncoming) :
    Tendsto (fun i => Real.sqrt (m.marker i:ℝ)*m.quarter i) atTop atTop := by
  apply tendsto_atTop_mono _ m.unbounded_marker
  intro i
  let b : ℝ := m.marker i
  have bp : 0 < b := m.marker_pos big i
  have h := (a.time_bounds (m.marker i)).1
  have sq : (Real.sqrt b)^2 = b := Real.sq_sqrt bp.le
  have lo : b ≤ Real.sqrt b*c.time (m.marker i) := by
    rw [a.arclength,Real.sqrt_inv,div_inv_eq_mul]
    change b ≤ Real.sqrt b * (a.slow _ * Real.sqrt b)
    nlinarith only [sq,mul_le_mul_of_nonneg_right h.le (sq_nonneg (Real.sqrt b))]
  have pos := mul_nonneg (Real.sqrt_nonneg b) (m.flight_positive i).le
  change b ≤ Real.sqrt b*(c.time (m.marker i)+f.length (m.seamParameter i))
  linarith only [lo,pos,mul_add (Real.sqrt b) (c.time (m.marker i)) (f.length (m.seamParameter i))]

theorem fast_parameters_vanish :
    Tendsto (fun i => (((m.marker i:ℝ)^2)⁻¹)) atTop (𝓝 0) := by
  simpa only [Function.comp_apply,←inv_pow,zero_pow (by decide : (2:ℕ) ≠ 0)] using
    (tendsto_inv_atTop_zero.comp m.unbounded_marker).pow 2

end ClosedSimilarity.GlobalSupport.MovingSeam.MatchedSequence
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.MatchedSequence.profiles
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.MatchedSequence.fast_seams_diverge
