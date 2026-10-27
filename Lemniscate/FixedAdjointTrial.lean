import Lemniscate.IntervalExtras

/-! The fixed rational coefficients in the current manuscript. A coarse
two-term comparison suffices to show that normalization decreases the residual. -/
namespace Lemniscate.CoarseArithmetic

def adjointTrialCoefficient (j : Fin 18) : ℚ :=
  ([1000000000000000000000000000000,
    223736893583674184592308357848,
    25484116510325630830715754968,
    2190873053796174749234141508,
    161421647978782201997701738,
    10787439027218763764207084,
    673940800112670696939420,
    40078659602346258076540,
    2295359309194503539129,
    127610930585485117011,
    6926090559231763880,
    368527953125777481,
    19284837011823255,
    994943639173809,
    50707140205575,
    2556901815584,
    127730370919,
    6327142260] : List ℚ).getD j.val 0 / 10^30

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem adjoint_trial_coefficient_bounds :
    adjointTrialCoefficient 0 = 1 ∧ (1/5:ℚ) < adjointTrialCoefficient 1 ∧
      ∀ j : Fin 18, 0 < adjointTrialCoefficient j := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem trial_normalization_coarse_comparisons :
    (71/100:ℚ) < rlo ∧ 0 < hLower 0 ∧ hUpper 0 < (23/50:ℚ) ∧
      (31/125:ℚ) < hLower 1 ∧ (21/1000:ℚ) < hLower 2 := by decide +kernel

end Lemniscate.CoarseArithmetic
