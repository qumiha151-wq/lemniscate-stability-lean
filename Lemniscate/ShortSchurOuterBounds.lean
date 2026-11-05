import Lemniscate.ShortSchurTransformNorms
import Lemniscate.ShortSchurTailBounds
import Lemniscate.ShortSchurKernel

namespace Lemniscate.CoarseArithmetic
open Matrix Finset

def shortOutsideEnvelope (l : ℕ) : ℝ := (H:ℝ)*((l:ℝ)+7)*(qb:ℝ)^(l-7)

theorem short_outside_envelope_nonneg (l : ℕ) : 0 ≤ shortOutsideEnvelope l := by
  unfold shortOutsideEnvelope
  have hH : (0:ℝ) ≤ (H:ℝ) := by norm_num [H,rhi,qb]
  have hq : (0:ℝ) ≤ (qb:ℝ) := by norm_num [qb]
  positivity

theorem short_abs_sum_product_bound {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (C M : ℝ) (hu : (∑ i, |u i|) ≤ C)
    (hv : ∀ i, |v i| ≤ M) (hM : 0 ≤ M) : |∑ i, u i*v i| ≤ C*M := by
  calc
    _ ≤ ∑ i, |u i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |u i| * |v i| := by simp only [abs_mul]
    _ ≤ ∑ i, |u i| * M := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _))
    _ = (∑ i, |u i|) * M := by rw [Finset.sum_mul]
    _ ≤ C*M := mul_le_mul_of_nonneg_right hu hM

theorem short_outside_h_column_bound (k : Fin 3) (i : Fin 15) (m : ℤ) (l : ℕ)
    (hm : m.natAbs=l) (hl : 15≤l) :
    |shortOutsideHColumn lemniscateFrequencySquared shortActualCoefficient k m i| ≤
      3200*(2*(m:ℝ))^2*shortOutsideEnvelope l := by
  let M := (2*(m:ℝ))^2*shortOutsideEnvelope l
  have hM : 0 ≤ M := mul_nonneg (sq_nonneg _) (short_outside_envelope_nonneg l)
  have hm' : (2*m).natAbs=2*l := by norm_num [Int.natAbs_mul, hm]
  have hA (a : Fin 15) (j : Fin 5) :
      |shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j (shortHeadFrequency a) (2*m)| ≤ 32*M ∧
      |shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j (2*m) (shortHeadFrequency a)| ≤ 32*M := by
    have ha : (shortHeadFrequency a).natAbs≤14 := by
      dsimp only [shortHeadFrequency]
      omega
    rw [show shortActualCoefficient = fourierCoefficient lemniscateFrequencySquared nome from rfl]
    simpa only [M, shortOutsideEnvelope, Int.cast_mul, Int.cast_ofNat,
      mul_assoc] using short_actual_bloch_outside_bound j (shortHeadFrequency a) (2*m) l ha hm' hl
  have hU : (∑ a : Fin 15, |shortHouseholder shortActualCoefficient i a|) ≤ 100 := by
    simpa [shortTransformReal, shortTransformL1Bound] using (short_transform_l1_bound 0 i).1
  have hL : (∑ a : Fin 15, |(shortHouseholder shortActualCoefficient * shortNeutral shortActualCoefficient) i a|) ≤ 100 := by
    simpa [shortTransformReal, shortTransformL1Bound, shortStageUTReal] using (short_transform_l1_bound 1 i).1
  have hR : (∑ a : Fin 15, |(shortNeutralInv shortActualCoefficient * shortHouseholder shortActualCoefficient) a i|) ≤ 100 := by
    simpa [shortTransformReal, shortTransformL1Bound, shortStageTiUReal] using (short_transform_l1_bound 2 i).2
  by_cases hk : k=0
  · subst k
    have havg (a : Fin 15) :
        |(shortBlochEntry lemniscateFrequencySquared shortActualCoefficient 0 (shortHeadFrequency a) (2*m)+
          shortBlochEntry lemniscateFrequencySquared shortActualCoefficient 0 (2*m) (shortHeadFrequency a))/2| ≤ 32*M := by
      rw [abs_div]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hsum := abs_add_le
        (shortBlochEntry lemniscateFrequencySquared shortActualCoefficient 0 (shortHeadFrequency a) (2*m))
        (shortBlochEntry lemniscateFrequencySquared shortActualCoefficient 0 (2*m) (shortHeadFrequency a))
      have ha := hA a 0
      linarith
    have hh := short_abs_sum_product_bound _ _ 100 (32*M) hU havg (by positivity)
    have hh' := hh.trans_eq (show 100*(32*M)=3200*(2*(m:ℝ))^2*shortOutsideEnvelope l by
      dsimp only [M]
      ring)
    simpa [shortOutsideHColumn] using hh'
  · have hleft := short_abs_sum_product_bound _ _ 100 (32*M) hL
      (fun a => (hA a (k.castLE (by decide : 3≤5))).1) (by positivity)
    have hright := short_abs_sum_product_bound _ _ 100 (32*M) hR
      (fun a => (hA a (k.castLE (by decide : 3≤5))).2) (by positivity)
    simp only [shortOutsideHColumn, if_neg hk, Finset.sum_add_distrib, abs_div]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hs := abs_add_le
      (∑ a : Fin 15, (shortHouseholder shortActualCoefficient * shortNeutral shortActualCoefficient) i a *
        shortBlochEntry lemniscateFrequencySquared shortActualCoefficient (k.castLE (by decide : 3≤5))
          (shortHeadFrequency a) (2*m))
      (∑ a : Fin 15, (shortNeutralInv shortActualCoefficient * shortHouseholder shortActualCoefficient) a i *
        shortBlochEntry lemniscateFrequencySquared shortActualCoefficient (k.castLE (by decide : 3≤5))
          (2*m) (shortHeadFrequency a))
    dsimp only [M] at hleft hright
    linarith

theorem short_outside_g_column_bound (k : Fin 3) (i : Fin 15) (m : ℤ) (l : ℕ)
    (hm : m.natAbs=l) (hl : 15≤l) :
    |shortOutsideGColumn lemniscateFrequencySquared shortActualCoefficient k m i| ≤
      12800*(2*(m:ℝ))^2*shortOutsideEnvelope l := by
  let M := (2*(m:ℝ))^2*shortOutsideEnvelope l
  have hM : 0 ≤ M := mul_nonneg (sq_nonneg _) (short_outside_envelope_nonneg l)
  have hH (a : Fin 15) (j : Fin 3) :
      |shortOutsideHColumn lemniscateFrequencySquared shortActualCoefficient j m a| ≤ 3200*M := by
    simpa only [M, mul_assoc] using short_outside_h_column_bound j a m l hm hl
  have hP : (∑ a : Fin 15, |shortStableProjection i a|) ≤ 2 := by
    have hh := (short_transform_l1_bound 3 i).1
    change (∑ a : Fin 15, |shortStableProjection i a|) ≤ 2 at hh
    exact hh
  have hP0 : (∑ a : Fin 15, |shortCenterProjection i a|) ≤ 2 := by
    have hh := (short_transform_l1_bound 4 i).1
    change (∑ a : Fin 15, |shortCenterProjection i a|) ≤ 2 at hh
    exact hh
  have hS := short_abs_sum_product_bound _ _ 2 (3200*M) hP
    (fun a => hH a k) (by positivity)
  by_cases hk : k.val<2
  · have hZ := short_abs_sum_product_bound _ _ 2 (3200*M) hP0
      (fun a => hH a ⟨k.val+1, by omega⟩) (by positivity)
    simp only [shortOutsideGColumn, dif_pos hk, Pi.add_apply, Matrix.mulVec, dotProduct]
    have hs := abs_add_le
      (∑ a : Fin 15, shortStableProjection i a *
        shortOutsideHColumn lemniscateFrequencySquared shortActualCoefficient k m a)
      (∑ a : Fin 15, shortCenterProjection i a *
        shortOutsideHColumn lemniscateFrequencySquared shortActualCoefficient ⟨k.val+1, by omega⟩ m a)
    dsimp only [M] at hS hZ
    linarith
  · simp only [shortOutsideGColumn, dif_neg hk, Pi.add_apply, Pi.zero_apply, add_zero,
      Matrix.mulVec, dotProduct]
    dsimp only [M] at hS hM
    nlinarith

set_option maxRecDepth 100000 in
theorem short_three_bernstein_weights : ∀ j : Fin 5,
    (∑ k : Fin 3, |shortBernsteinWeight j (k.castLE (by decide : 3≤5))|) ≤ (7/4:ℚ) := by
  decide +kernel

theorem short_outside_bernstein_bound (j : Fin 5) (i : Fin 15) (m : ℤ) (l : ℕ)
    (hm : m.natAbs=l) (hl : 15≤l) :
    |shortOutsideBernsteinColumn lemniscateFrequencySquared shortActualCoefficient j m i| ≤
      22400*(2*(m:ℝ))^2*shortOutsideEnvelope l := by
  let M := (2*(m:ℝ))^2*shortOutsideEnvelope l
  have hM : 0 ≤ M := mul_nonneg (sq_nonneg _) (short_outside_envelope_nonneg l)
  have hweights : (∑ k : Fin 3, |(shortBernsteinWeight j (k.castLE (by decide : 3≤5)):ℝ)|) ≤ 7/4 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (short_three_bernstein_weights j)
    simpa only [Rat.cast_sum, Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using h
  have hG (k : Fin 3) :
      |shortOutsideGColumn lemniscateFrequencySquared shortActualCoefficient k m i| ≤ 12800*M := by
    simpa only [M, mul_assoc] using short_outside_g_column_bound k i m l hm hl
  have hh := short_abs_sum_product_bound _ _ (7/4) (12800*M) hweights hG (by positivity)
  change |∑ k : Fin 3, (shortBernsteinWeight j (k.castLE (by decide : 3≤5)):ℝ)*
    shortOutsideGColumn lemniscateFrequencySquared shortActualCoefficient k m i| ≤ _
  exact hh.trans_eq (by dsimp only [M]; ring)

end Lemniscate.CoarseArithmetic
