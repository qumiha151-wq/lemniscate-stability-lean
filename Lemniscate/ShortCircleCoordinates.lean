import Lemniscate.ShortCircleFourier
import Mathlib.Tactic.Module

namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Finset
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_short_sine_head (v : Fin 7 → ℝ) :
    I • circleSineTrialH4 T 7 (fun j => (v j:ℂ)) =
      circleShortHead T (fun i => (shortSineCoordinate v i:ℂ)) := by
  have hp (z : ℂ) : I*(z*evenSineFactor)=z*evenCosineFactor := by
    simp only [evenSineFactor]
    ring_nf
    simp [Complex.I_sq]
  simp only [circleSineTrialH4, Finset.smul_sum, circleSineH4, smul_smul, hp]
  norm_num [circleShortHead,shortSineCoordinate,shortHeadFrequency,Fin.sum_univ_succ,
    evenCosineFactor]
  push_cast
  module

theorem circle_short_rotation_head : circleShortRotationApproximation T =
    circleShortHead T (fun i => (shortRotationHead shortActualCoefficient i:ℂ)) :=
  circle_short_sine_head T _

theorem circle_short_adjoint_head : circleShortAdjointApproximation T =
    circleShortHead T (fun i => (shortAdjointHead shortActualCoefficient i:ℂ)) :=
  circle_short_sine_head T _

theorem circle_short_anchor_head : circleHouseholderAnchorH4 T =
    circleShortHead T (fun i => (shortAnchorHead i:ℂ)) := by
  apply Subtype.ext
  apply circle_fourier_ext T
  intro n
  rw [circle_householder_anchor_h4_coe,circle_householder_anchor_fourier,
    circle_short_head_fourier]
  norm_num [shortAnchorHead,shortSineCoordinate,shortHeadFrequency,
    Fin.sum_univ_succ,evenCosineFactor]
  split_ifs <;> push_cast <;> ring

theorem circle_short_rotation_fourier_at (i : Fin 15) :
    fourierCoeff (circleShortRotationApproximation T:CircleL2 T) (shortHeadFrequency i) =
      (shortRotationHead shortActualCoefficient i:ℂ) := by
  rw [circle_short_rotation_head,circle_short_head_fourier_at]

theorem circle_short_adjoint_fourier_at (i : Fin 15) :
    fourierCoeff (circleShortAdjointApproximation T:CircleL2 T) (shortHeadFrequency i) =
      (shortAdjointHead shortActualCoefficient i:ℂ) := by
  rw [circle_short_adjoint_head,circle_short_head_fourier_at]

end Lemniscate
