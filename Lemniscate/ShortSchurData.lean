import Lemniscate.Algebra
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases

/-! Small exact inputs for the new low/high proof.  These are the rational
trial itself and the seven-mode normalization formulas, not old certificate
entries.  Both the residual proof and the matrix proof use these definitions. -/
namespace Lemniscate
open Matrix Finset

def shortAdjointTrialNumerator : Fin 8 → ℚ :=
  ![10000000000, 2237368936, 254841165, 21908731, 1614216, 107874, 6739, 401]

noncomputable def shortAdjointTrialCoeff (j : Fin 8) : ℝ :=
  (shortAdjointTrialNumerator j : ℝ) / 10000000000

def shortHeadFrequency (i : Fin 15) : ℤ := 2*(i.val : ℤ)-14

def shortLowWeight (j : Fin 5) : Fin 7 → ℚ :=
  ![![21,1000,273,99,4,201,4],
    ![21,1000,277,111,107,208,55],
    ![19,1000,309,133,222,233,116],
    ![15,1000,379,201,366,284,195],
    ![12,1000,473,320,540,354,288]] j

noncomputable def shortRotationSine (h : ℕ → ℝ) (j : Fin 7) : ℝ :=
  let v : Fin 7 → ℝ := fun i => (i.val+1)*h (i.val+1)
  v j / Real.sqrt (∑ i, v i ^ 2)

noncomputable def shortAdjointSine (h : ℕ → ℝ) (j : Fin 7) : ℝ :=
  shortAdjointTrialCoeff j.castSucc /
    ∑ i : Fin 7, shortAdjointTrialCoeff i.castSucc * shortRotationSine h i

noncomputable def shortSineCoordinate (v : Fin 7 → ℝ) (i : Fin 15) : ℝ :=
  if hi : i.val < 7 then -v ⟨6-i.val, by omega⟩ / Real.sqrt 2
  else if hi : 7 < i.val then v ⟨i.val-8, by omega⟩ / Real.sqrt 2
  else 0

noncomputable def shortRotationHead (h : ℕ → ℝ) : Fin 15 → ℝ :=
  shortSineCoordinate (shortRotationSine h)

noncomputable def shortAdjointHead (h : ℕ → ℝ) : Fin 15 → ℝ :=
  shortSineCoordinate (shortAdjointSine h)

noncomputable def shortAnchorHead : Fin 15 → ℝ :=
  shortSineCoordinate (fun j => if j = 0 then 1 else 0)

theorem short_low_weight_pos (j : Fin 5) (i : Fin 7) : 0 < shortLowWeight j i := by
  fin_cases j <;> fin_cases i <;> norm_num [shortLowWeight]

end Lemniscate
