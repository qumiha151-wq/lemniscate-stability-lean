import Lemniscate.VectorIntervalData
import Lemniscate.RotationCoefficientTails
import Lemniscate.PeriodicAdjointTruncation

/-! Analytic soundness of the finite normalization certificate. Each
interval is connected to the actual real coefficient used in the paper. -/
namespace Lemniscate.CoarseArithmetic

theorem sum_interval_sound {ι : Type*} [Fintype ι] (I : ι → Interval) (f : ι → ℝ)
    (h : ∀ i, Contains (I i) (f i)) :
    Contains ⟨∑ i, (I i).lo, ∑ i, (I i).hi⟩ (∑ i, f i) := by
  constructor <;> simp only [Rat.cast_sum]
  · exact Finset.sum_le_sum (fun i _ => (h i).1)
  · exact Finset.sum_le_sum (fun i _ => (h i).2)

theorem rotation_norm_data_sound : Contains rotationNormData rotationCoefficientNorm := by
  have hc : Contains (fineCoefficientData 0) (constantCoefficient thetaParameter nome) := by
    simpa [fourierCoefficient] using fine_coefficient_data_sound ⟨0,by decide⟩
  have hr : Contains ⟨thetaRLower,thetaRUpper⟩ thetaParameter := actual_nome_theta_r_bounds
  have hx := dividePositive_sound _ _ _ _ vector_interval_certificate.r_pos
    (scale_sound _ _ 2 hc) (scale_sound _ _ 5 hr)
  have hx' : Contains rotationNormSquaredInput
      (2*constantCoefficient thetaParameter nome/(5*thetaParameter)) := by
    simpa only [rotationNormSquaredInput,Rat.cast_ofNat,mul_comm] using hx
  exact sqrt_enclosure_sound _ _ _ _ hx'
    vector_interval_certificate.norm_pos.le vector_interval_certificate.norm_hi_pos.le
    vector_interval_certificate.norm_lower vector_interval_certificate.norm_upper

theorem rotation_coefficient_data_sound (j : Fin 18) :
    Contains (rotationCoefficientData j) (rotationSineCoefficient j.val) := by
  have hc : Contains (fineCoefficientData (j.val+1))
      (evenCoefficient thetaParameter nome (j.val+1)) := by
    simpa only [fourierCoefficient,if_neg (by omega : j.val+1 ≠ 0)] using
      fine_coefficient_data_sound ⟨j.val+1,by omega⟩
  have hx := dividePositive_sound _ _ _ _ vector_interval_certificate.norm_pos
    (scale_sound _ _ (2*(j.val+1:ℕ)) hc) rotation_norm_data_sound
  have hx' : Contains (dividePositive
      (scale (fineCoefficientData (j.val+1)) (2*(j.val+1:ℕ))) rotationNormData)
      (rotationSineCoefficient j.val) := by
    simpa only [rotationSineCoefficient,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,mul_comm] using hx
  exact hx'.mono (vector_interval_certificate.coefficients j).1
    (vector_interval_certificate.coefficients j).2

theorem trial_pairing_data_sound : Contains trialPairingData adjointTrialPairing := by
  have hx := sum_interval_sound
    (fun j : Fin 18 => scale (rotationCoefficientData j) (adjointTrialCoefficient j))
    (fun j => rotationSineCoefficient j.val*(adjointTrialCoefficient j:ℝ))
    (fun j => scale_sound _ _ _ (rotation_coefficient_data_sound j))
  have heq : (∑ j : Fin 18, rotationSineCoefficient j.val*(adjointTrialCoefficient j:ℝ)) =
      adjointTrialPairing := by
    simp only [rotationSineCoefficient,adjointTrialPairing,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at hx
  exact hx.mono vector_interval_certificate.pair.1 vector_interval_certificate.pair.2

theorem adjoint_coefficient_data_sound (j : Fin 18) :
    Contains (adjointCoefficientData j) (adjointNormalizedCoefficient j) := by
  have hx := dividePositive_sound _ _ _ _ vector_interval_certificate.pair_pos
    (point_sound (adjointTrialCoefficient j)) trial_pairing_data_sound
  exact hx.mono (vector_interval_certificate.adjoint_coefficients j).1
    (vector_interval_certificate.adjoint_coefficients j).2

noncomputable def rotationFiniteNorm : ℝ :=
  Real.sqrt (∑ j : Fin 15, (rotationSineCoefficient j.val)^2)

noncomputable def rotationFiniteCoefficient (j : Fin 15) : ℝ :=
  rotationSineCoefficient j.val/rotationFiniteNorm

noncomputable def adjointFinitePairing : ℝ :=
  ∑ j : Fin 15, adjointNormalizedCoefficient (Fin.castAdd 3 j)*rotationFiniteCoefficient j

noncomputable def adjointFiniteCoefficient (j : Fin 15) : ℝ :=
  adjointNormalizedCoefficient (Fin.castAdd 3 j)/adjointFinitePairing

noncomputable def finiteDifferenceCoefficient (j : Fin 15) : ℝ :=
  adjointFiniteCoefficient j-rotationFiniteCoefficient j

theorem rotation_finite_norm_data_sound : Contains rotationFiniteNormData rotationFiniteNorm := by
  have hx := sum_interval_sound
    (fun j : Fin 15 => mul (rotationCoefficientData (Fin.castAdd 3 j))
      (rotationCoefficientData (Fin.castAdd 3 j)))
    (fun j => (rotationSineCoefficient j.val)^2)
    (fun j => by
      have h := mul_sound _ _ _ _
        (rotation_coefficient_data_sound (Fin.castAdd 3 j))
        (rotation_coefficient_data_sound (Fin.castAdd 3 j))
      simpa only [pow_two,Fin.val_castAdd] using h)
  exact sqrt_enclosure_sound _ _ _ _ hx
    ((by norm_num : (0:ℚ) ≤ 999/1000).trans vector_interval_certificate.finite_norm_pos.le)
    vector_interval_certificate.finite_norm_hi_pos.le
    vector_interval_certificate.finite_norm_lower vector_interval_certificate.finite_norm_upper

theorem rotation_finite_data_sound (j : Fin 15) :
    Contains (rotationFiniteData j) (rotationFiniteCoefficient j) := by
  have hp : 0 < rotationFiniteNormData.lo :=
    (by norm_num : (0:ℚ) < 999/1000).trans vector_interval_certificate.finite_norm_pos
  have hx := dividePositive_sound _ _ _ _ hp
    (rotation_coefficient_data_sound (Fin.castAdd 3 j)) rotation_finite_norm_data_sound
  exact hx.mono (vector_interval_certificate.rotation_finite j).1
    (vector_interval_certificate.rotation_finite j).2

theorem adjoint_finite_pairing_data_sound : Contains adjointFinitePairingData adjointFinitePairing := by
  have hx := sum_interval_sound
    (fun j : Fin 15 => mul (adjointCoefficientData (Fin.castAdd 3 j)) (rotationFiniteData j))
    (fun j => adjointNormalizedCoefficient (Fin.castAdd 3 j)*rotationFiniteCoefficient j)
    (fun j => mul_sound _ _ _ _ (adjoint_coefficient_data_sound (Fin.castAdd 3 j))
      (rotation_finite_data_sound j))
  exact hx.mono vector_interval_certificate.finite_pair.1 vector_interval_certificate.finite_pair.2

theorem adjoint_finite_data_sound (j : Fin 15) :
    Contains (adjointFiniteData j) (adjointFiniteCoefficient j) := by
  have hp : 0 < adjointFinitePairingData.lo :=
    (by norm_num : (0:ℚ) < 999/1000).trans vector_interval_certificate.finite_pair_pos
  have hx := dividePositive_sound _ _ _ _ hp
    (adjoint_coefficient_data_sound (Fin.castAdd 3 j)) adjoint_finite_pairing_data_sound
  exact hx.mono (vector_interval_certificate.adjoint_finite j).1
    (vector_interval_certificate.adjoint_finite j).2

theorem difference_finite_data_sound (j : Fin 15) :
    Contains (differenceFiniteData j) (finiteDifferenceCoefficient j) := by
  have hx := add_sound _ _ _ _ (adjoint_finite_data_sound j)
    (scale_sound _ _ (-1) (rotation_finite_data_sound j))
  have hx' : Contains (add (adjointFiniteData j) (scale (rotationFiniteData j) (-1)))
      (finiteDifferenceCoefficient j) := by
    simpa only [finiteDifferenceCoefficient,Rat.cast_neg,Rat.cast_one,mul_neg_one,sub_eq_add_neg] using hx
  exact hx'.mono (vector_interval_certificate.difference_finite j).1
    (vector_interval_certificate.difference_finite j).2

theorem sqrt_two_data_sound : Contains sqrtTwoData (Real.sqrt 2) := by
  exact sqrt_enclosure_sound (point 2) 2 _ _ (point_sound 2)
    vector_interval_certificate.sqrt_two_pos.le vector_interval_certificate.sqrt_two_hi_pos.le
    vector_interval_certificate.sqrt_two_lower vector_interval_certificate.sqrt_two_upper

end Lemniscate.CoarseArithmetic
