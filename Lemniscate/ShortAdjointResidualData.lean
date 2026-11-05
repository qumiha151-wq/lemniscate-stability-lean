import Lemniscate.ShortFourierEnclosure
import Lemniscate.ShortSchurData
import Lemniscate.GeometricMomentTails

/-! Exact arithmetic for the new eight-mode unnormalized trial. The intervals
are computed from the new ten-decimal scalar boxes and the actual Fourier
enclosures, not copied from the former eighteen-mode certificate. -/
namespace Lemniscate.CoarseArithmetic
open Finset

def shortTrialRationalCoeff (i : Fin 8) : ℚ :=
  shortAdjointTrialNumerator i / 10000000000

def shortHInterval (j : ℕ) : Interval :=
  if j = 0 then shortConstantInterval else shortPositiveInterval j

def shortTrialSineEntry (i j : ℕ) : Interval :=
  let n : ℚ := 2*i
  let m : ℚ := 2*j
  let v := scale (mul shortFrequencyInterval
    (add (scale (shortHInterval (i-j+(j-i))) (7*m-n))
      (scale (shortHInterval (i+j)) (7*m+n)))) ((15/2:ℚ)*n)
  if i = j then add v
    ⟨-4*shortFrequencyInterval.hi^2*n^4-42,
      -4*shortFrequencyInterval.lo^2*n^4-42⟩ else v

def shortRawResidualInterval (j : Fin 16) : Interval :=
  ⟨∑ i : Fin 8, (scale (shortTrialSineEntry (i.val+1) (j.val+1))
      (shortTrialRationalCoeff i)).lo,
    ∑ i : Fin 8, (scale (shortTrialSineEntry (i.val+1) (j.val+1))
      (shortTrialRationalCoeff i)).hi⟩

def shortResidualWeight (j : ℕ) : ℚ := (13/100:ℚ)*(2*j)^4+75/2

def shortResidualHeadBound : ℚ :=
  ∑ j : Fin 16, (absUpper (shortRawResidualInterval j))^2 /
    shortResidualWeight (j.val+1)

def shortResidualTailBound : ℚ :=
  (480*rhi*H*(∑ i : Fin 8, shortTrialRationalCoeff i))^2 *
    momentTail 2 (qb^2) 17 / ((52/25:ℚ)*qb^16)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_trial_rational_positive :
    shortTrialRationalCoeff 0 = 1 ∧ (1/5:ℚ) < shortTrialRationalCoeff 1 ∧
      ∀ i : Fin 8, 0 < shortTrialRationalCoeff i := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_pairing_coarse_comparisons :
    (71/100:ℚ) < shortFrequencyInterval.lo ∧
      0 < shortConstantInterval.lo ∧ shortConstantInterval.hi < (23/50:ℚ) ∧
      (31/125:ℚ) < (shortPositiveInterval 1).lo ∧
      (21/1000:ℚ) < (shortPositiveInterval 2).lo := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_residual_head_comparison :
    shortResidualHeadBound < (1/(5*10^10):ℚ) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_residual_tail_comparison :
    shortResidualTailBound < (1/(3*10^15):ℚ) := by decide +kernel

theorem short_residual_total_comparison :
    shortResidualHeadBound+shortResidualTailBound < (1/200000:ℚ)^2 := by
  have h := short_residual_head_comparison
  have t := short_residual_tail_comparison
  linarith

end Lemniscate.CoarseArithmetic
