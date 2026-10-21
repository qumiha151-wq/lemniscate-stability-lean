import Lemniscate.EvenSineFamily
import Lemniscate.PeriodicCosineSpace

/-! Realize the full positive even-frequency sine sequence space as actual
periodic L2 functions with normalized Haar measure. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleEvenSineMode (j : ℕ) : CircleL2 T :=
  evenSineMode (fourierBasis (T := T)) j

theorem circle_even_sine_orthonormal : Orthonormal ℂ (circleEvenSineMode T) :=
  even_sine_orthonormal (fourierBasis (T := T)) (fourierBasis (T := T)).orthonormal

noncomputable def circleEvenSineSynthesis : SineSequenceSpace →ₗᵢ[ℂ] CircleL2 T :=
  evenSineSynthesis (fourierBasis (T := T)) (fourierBasis (T := T)).orthonormal

theorem circle_even_sine_hasSum (v : SineSequenceSpace) :
    HasSum (fun j : ℕ => v j • circleEvenSineMode T j) (circleEvenSineSynthesis T v) :=
  even_sine_hasSum (fourierBasis (T := T)) (fourierBasis (T := T)).orthonormal v

theorem circle_even_sine_norm_sq (v : SineSequenceSpace) :
    ‖circleEvenSineSynthesis T v‖^2 = ∑' j : ℕ, ‖v j‖^2 := by
  rw [(circleEvenSineSynthesis T).norm_map]
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) v
  simpa [Real.rpow_two] using h

theorem circle_even_sine_mode_coeff (j : ℕ) (n : ℤ) :
    fourierCoeff (circleEvenSineMode T j) n =
      evenSineFactor*((if n = 2*((j+1:ℕ):ℤ) then 1 else 0)-
        (if n = -(2*((j+1:ℕ):ℤ)) then 1 else 0)) := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  have hg := orthonormal_iff_ite.mp (fourierBasis (T := T)).orthonormal
  simp only [circleEvenSineMode, evenSineMode, inner_smul_right, inner_sub_right, hg]

end Lemniscate
