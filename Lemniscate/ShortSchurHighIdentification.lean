import Lemniscate.ShortSchurHighArithmetic
import Lemniscate.ShortSchurIdentification

/-! The external matrix computation is the actual full finite-rank kernel,
not a separate finite-dimensional model. -/
namespace Lemniscate.CoarseArithmetic
open Matrix Finset

private theorem short_cast_three_one (h : 3≤5) : Fin.castLE h (1:Fin 3) = (1:Fin 5) := by
  apply Fin.ext
  rfl
private theorem short_cast_three_two (h : 3≤5) : Fin.castLE h (2:Fin 3) = (2:Fin 5) := by
  apply Fin.ext
  rfl

theorem short_high_h0_identification (i : Fin 15) (b : Fin 14) :
    shortHighH0Real i b = shortOutsideHColumn lemniscateFrequencySquared
      shortActualCoefficient 0 (shortOutsideHalfFrequency b) i := by
  change (shortHouseholder shortActualCoefficient *
    ((1/2:ℝ) • (shortOutsideForward 0 + shortOutsideBackward 0))) i b = _
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    shortOutsideForward, shortOutsideBackward, shortOutsideHColumn, if_pos rfl]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem short_high_h1_identification (i : Fin 15) (b : Fin 14) :
    shortHighH1Real i b = shortOutsideHColumn lemniscateFrequencySquared
      shortActualCoefficient 1 (shortOutsideHalfFrequency b) i := by
  change ((1/2:ℝ) •
    ((shortHouseholder shortActualCoefficient * shortNeutral shortActualCoefficient) * shortOutsideForward 1 +
      (shortNeutralInv shortActualCoefficient * shortHouseholder shortActualCoefficient)ᵀ * shortOutsideBackward 1)) i b = _
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, transpose_apply, smul_eq_mul,
    shortOutsideForward, shortOutsideBackward, shortOutsideHColumn,
    if_neg (by decide : (1:Fin 3)≠0), Finset.sum_add_distrib, short_cast_three_one]
  ring

theorem short_high_h2_identification (i : Fin 15) (b : Fin 14) :
    shortHighH2Real i b = shortOutsideHColumn lemniscateFrequencySquared
      shortActualCoefficient 2 (shortOutsideHalfFrequency b) i := by
  change ((1/2:ℝ) •
    ((shortHouseholder shortActualCoefficient * shortNeutral shortActualCoefficient) * shortOutsideForward 2 +
      (shortNeutralInv shortActualCoefficient * shortHouseholder shortActualCoefficient)ᵀ * shortOutsideBackward 2)) i b = _
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, transpose_apply, smul_eq_mul,
    shortOutsideForward, shortOutsideBackward, shortOutsideHColumn,
    if_neg (by decide : (2:Fin 3)≠0), Finset.sum_add_distrib, short_cast_three_two]
  ring

noncomputable def shortHighGVector : Fin 3 → Matrix (Fin 15) (Fin 14) ℝ :=
  ![shortHighG0Real,shortHighG1Real,shortHighPH2Real]

theorem short_high_g_identification (k : Fin 3) (i : Fin 15) (b : Fin 14) :
    shortHighGVector k i b = shortOutsideGColumn lemniscateFrequencySquared
      shortActualCoefficient k (shortOutsideHalfFrequency b) i := by
  fin_cases k
  · change (shortStableProjection * shortHighH0Real + shortCenterProjection * shortHighH1Real) i b = _
    simp only [Matrix.add_apply, Matrix.mul_apply]
    simp_rw [short_high_h0_identification, short_high_h1_identification]
    simp [shortOutsideGColumn, Matrix.mulVec, dotProduct]
  · change (shortStableProjection * shortHighH1Real + shortCenterProjection * shortHighH2Real) i b = _
    simp only [Matrix.add_apply, Matrix.mul_apply]
    simp_rw [short_high_h1_identification, short_high_h2_identification]
    simp [shortOutsideGColumn, Matrix.mulVec, dotProduct]
  · change (shortStableProjection * shortHighH2Real) i b = _
    simp only [Matrix.mul_apply]
    simp_rw [short_high_h2_identification]
    simp [shortOutsideGColumn, Matrix.mulVec, dotProduct]

theorem short_exterior_b_identification (j : Fin 5) (i : Fin 15) (b : Fin 14) :
    shortExteriorBReal j i b = shortOutsideBernsteinColumn lemniscateFrequencySquared
      shortActualCoefficient j (shortOutsideHalfFrequency b) i := by
  unfold shortOutsideBernsteinColumn
  simp_rw [← short_high_g_identification]
  fin_cases j <;>
    norm_num [shortExteriorBReal, shortHighGVector, shortBernsteinWeight,
      Fin.sum_univ_succ, Nat.choose, Fin.castLE, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      shortExteriorB0Real,shortExteriorB1Real,shortExteriorB2Real,shortExteriorB3Real,shortExteriorB4Real,
      shortHighExtB0term0Real,
      shortHighExtB1term0Real,shortHighExtB1term1Real,shortHighExtB1sum1Real,
      shortHighExtB2term0Real,shortHighExtB2term1Real,shortHighExtB2term2Real,
      shortHighExtB2sum1Real,shortHighExtB2sum2Real,
      shortHighExtB3term0Real,shortHighExtB3term1Real,shortHighExtB3term2Real,
      shortHighExtB3sum1Real,shortHighExtB3sum2Real,
      shortHighExtB4term0Real,shortHighExtB4term1Real,shortHighExtB4term2Real,
      shortHighExtB4sum1Real,shortHighExtB4sum2Real] <;> ring

theorem short_raw_high_identification (j : Fin 5) :
    shortRawHighReal j = shortRawOutsideBernstein j := by fin_cases j <;> rfl

noncomputable def shortSelectedHighReal (j : Fin 5) (i k : Fin 22) : ℝ :=
  match shortHighLookup i, shortHighLookup k with
  | .inl a, .inl b => shortBReal j a b
  | .inl a, .inr b => shortExteriorBReal j a b
  | .inr b, .inl a => shortExteriorBReal j a b
  | .inr a, .inr b => shortRawHighReal j a b

theorem short_selected_high_identification (j : Fin 5) (i k : Fin 22) :
    shortSelectedHighReal j i k = shortBernsteinKernel lemniscateFrequencySquared
      shortActualCoefficient j (shortHighHalfFrequency i) (shortHighHalfFrequency k) := by
  have hi := short_high_lookup_spec i
  have hk := short_high_lookup_spec k
  unfold shortSelectedHighReal
  cases hli : shortHighLookup i <;> cases hlk : shortHighLookup k
  all_goals simp only [hli, hlk] at hi hk
  · rw [shortBernsteinKernel, hi, hk]
    exact congrFun (congrFun (short_bernstein_identification j) _) _
  · rw [shortBernsteinKernel, hi, hk.1, ← hk.2]
    exact short_exterior_b_identification j _ _
  · rw [shortBernsteinKernel, hi.1, hk, ← hi.2]
    exact short_exterior_b_identification j _ _
  · rw [shortBernsteinKernel, hi.1, hk.1, ← hi.2, ← hk.2, short_raw_high_identification]
    rfl

end Lemniscate.CoarseArithmetic
