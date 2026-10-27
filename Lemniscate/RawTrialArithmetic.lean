import Lemniscate.FineCoefficientData
import Lemniscate.FixedAdjointTrial
import Lemniscate.GeometricMomentTails

/-! Exact finite comparisons for the unnormalized rational trial. The
normalization pairing is greater than one, so no square roots or uncertain
divisions enter this residual calculation. Analytic soundness is separate. -/
namespace Lemniscate.CoarseArithmetic
open Finset

def rawTrialSineEntry (i j : ℕ) : Interval :=
  let n : ℚ := 2*(i:ℚ)
  let m : ℚ := 2*(j:ℚ)
  let v := scale (mul ⟨thetaRLower,thetaRUpper⟩
    (add (scale (fineCoefficientData (i-j+(j-i))) (7*m-n))
         (scale (fineCoefficientData (i+j)) (7*m+n)))) ((15/2:ℚ)*n)
  if i = j then add v ⟨-4*thetaRUpper^2*n^4-42,-4*thetaRLower^2*n^4-42⟩ else v

def rawTrialResidualInterval (j : Fin 40) : Interval :=
  ⟨∑ i : Fin 18, (scale (rawTrialSineEntry (i.val+1) (j.val+1)) (adjointTrialCoefficient i)).lo,
   ∑ i : Fin 18, (scale (rawTrialSineEntry (i.val+1) (j.val+1)) (adjointTrialCoefficient i)).hi⟩

def rawTrialResidualBound (j : Fin 40) : ℚ :=
  ([2607383565754,4919593767325,2810420966641,814941261507,158567028174,23776991614,2968569859,323554708,31678233,2978857,372287,333170,111039,332714,484085,492053,311126,918718,1330430644870174,76006685216968,4158263175333,220624780629,11439935176,582657862,29259412,1462376,83628,16400,13574,13878,14333,14795,15257,15719,16181,16644,17106,17568,18031,18493] : List ℚ).getD j.val 0/10^30

def rawTrialTailBound : ℚ :=
  (480*rhi*H*(∑ i : Fin 18, adjointTrialCoefficient i))^2*
    momentTail 6 (qb^2) 41/qb^36

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raw_trial_residual_comparisons : ∀ j : Fin 40,
    absUpper (rawTrialResidualInterval j) ≤ rawTrialResidualBound j := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raw_trial_residual_square_comparison :
    (∑ j : Fin 40, (rawTrialResidualBound j)^2)+rawTrialTailBound < 2/10^30 := by decide +kernel

end Lemniscate.CoarseArithmetic
