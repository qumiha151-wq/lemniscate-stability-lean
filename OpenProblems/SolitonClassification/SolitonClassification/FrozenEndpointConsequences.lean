import SolitonClassification.FrozenSeamSection
import SolitonClassification.FrozenTailSigns

/-! Transport of the terminal signs to both unbounded time directions for
the canonical actual seams and to the intermediate-value shooting statement. -/
namespace ClosedSimilarity.FrozenStress.Endpoint
open GlobalSupport

structure TerminalBounds : Prop where
  negative : 13 < -(seam (-1/4)).radial 20 ∧
    -0.10 < (seam (-1/4)).J 20 ∧ (seam (-1/4)).J 20 < -0.09
  positive : 12 < -(seam 1).radial 20 ∧ 0.8 < (seam 1).J 20

theorem TerminalBounds.both_tails (data : TerminalBounds) (s : ℝ) (hs : 20≤|s|) :
    (seam (-1/4)).rawI s < -0.002 ∧ 0.52 < (seam 1).rawI s := by
  have one (t : ℝ) (ht : 20≤t) :
      (seam (-1/4)).rawI t < -0.002 ∧ 0.52 < (seam 1).rawI t :=
    ⟨(seam (-1/4)).negative_raw_tail data.negative.1 data.negative.2.1 data.negative.2.2 ht,
     (seam 1).positive_raw_tail data.positive.1 data.positive.2 ht⟩
  by_cases nonnegative : 0≤s
  · exact one s (by simpa only [abs_of_nonneg nonnegative] using hs)
  have back := one (-s) (by simpa only [abs_of_neg (lt_of_not_ge nonnegative)] using hs)
  have parity (c : ℝ) : (seam c).rawI (-s) = (seam c).rawI s :=
    ((seam c).seam_impact_radial_parity (seam_initial c).2.1 (seam_initial c).2.2.2 s).1
  simpa only [parity] using back

theorem TerminalBounds.opposite_sections (data : TerminalBounds) {t : ℝ} (ht : 20≤t) :
    ∃ c ∈ Set.Ioo (-1/4 : ℝ) 1,
      (seam c).transverse t=0 ∧ (seam c).transverse (-t)=0 ∧
      (seam c).radial t<0 ∧ 0<(seam c).radial (-t) := by
  have tails := data.both_tails t (ht.trans (le_abs_self _))
  exact transverse_zero_on_opposite_sections (by norm_num) (by linarith)
    (lt_trans tails.1 (by norm_num)) (lt_trans (by norm_num) tails.2)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.TerminalBounds.both_tails
#print axioms ClosedSimilarity.FrozenStress.Endpoint.TerminalBounds.opposite_sections
