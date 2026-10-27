import Lemniscate.FixedAdjointTrial
import Lemniscate.CoefficientMajorant

/-! A two-term lower bound for the trial pairing. The complete coefficient
sum is positive, so normalization can only decrease the adjoint residual. -/
namespace Lemniscate.CoarseArithmetic
open Finset

noncomputable def rotationCoefficientNorm : ℝ :=
  Real.sqrt (2*constantCoefficient thetaParameter nome/(5*thetaParameter))

theorem rotation_coefficient_norm_bounds :
    0 < rotationCoefficientNorm ∧ rotationCoefficientNorm < (51/100:ℝ) := by
  have hr := actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩)
    (by norm_num [rlo,thetaRLower]) (by norm_num [rhi,thetaRUpper])
  have hc : Contains (hInterval 0) (constantCoefficient thetaParameter nome) := by
    simpa [fourierCoefficient] using theta_nome_fourier_enclosure 0
  change (hLower 0:ℝ) ≤ constantCoefficient thetaParameter nome ∧
    constantCoefficient thetaParameter nome ≤ (hUpper 0:ℝ) at hc
  have hrat := trial_normalization_coarse_comparisons
  have hrl : ((71/100:ℚ):ℝ) < (rlo:ℝ) := Rat.cast_lt.mpr hrat.1
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hrl
  have hr0 : (71/100:ℝ) < thetaParameter := hrl.trans_le hr.1
  have hc0 : 0 < constantCoefficient thetaParameter nome :=
    (by exact_mod_cast hrat.2.1 : (0:ℝ) < (hLower 0:ℝ)).trans_le hc.1
  have hhu : (hUpper 0:ℝ) < ((23/50:ℚ):ℝ) := Rat.cast_lt.mpr hrat.2.2.1
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hhu
  have hcu : constantCoefficient thetaParameter nome < (23/50:ℝ) := hc.2.trans_lt hhu
  have hrpos : 0 < thetaParameter := by linarith
  have harg : 0 < 2*constantCoefficient thetaParameter nome/(5*thetaParameter) := by positivity
  have hupper : 2*constantCoefficient thetaParameter nome/(5*thetaParameter) ≤
      2*(23/50:ℝ)/(5*(71/100:ℝ)) := by
    exact div_le_div₀ (by positivity) (by linarith) (by norm_num) (by linarith)
  have hsq := Real.sq_sqrt harg.le
  have hn := Real.sqrt_nonneg (2*constantCoefficient thetaParameter nome/(5*thetaParameter))
  constructor
  · exact Real.sqrt_pos.mpr harg
  · dsimp only [rotationCoefficientNorm]
    nlinarith

noncomputable def adjointTrialPairing : ℝ :=
  (∑ j : Fin 18, (adjointTrialCoefficient j:ℝ)*
    (2*((j.val+1:ℕ):ℝ)*evenCoefficient thetaParameter nome (j.val+1))) /
      rotationCoefficientNorm

theorem adjoint_trial_pairing_gt_one : 1 < adjointTrialPairing := by
  have ht := adjoint_trial_coefficient_bounds
  have hrat := trial_normalization_coarse_comparisons
  have h1 := (theta_nome_fourier_enclosure 1).1
  have h2 := (theta_nome_fourier_enclosure 2).1
  change (hLower 1:ℝ) ≤ evenCoefficient thetaParameter nome 1 at h1
  change (hLower 2:ℝ) ≤ evenCoefficient thetaParameter nome 2 at h2
  have hh1 : ((31/125:ℚ):ℝ) < (hLower 1:ℝ) := Rat.cast_lt.mpr hrat.2.2.2.1
  have hh2 : ((21/1000:ℚ):ℝ) < (hLower 2:ℝ) := Rat.cast_lt.mpr hrat.2.2.2.2
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh1 hh2
  have h1' : (31/125:ℝ) < evenCoefficient thetaParameter nome 1 := hh1.trans_le h1
  have h2' : (21/1000:ℝ) < evenCoefficient thetaParameter nome 2 := hh2.trans_le h2
  have ht0 : (adjointTrialCoefficient 0:ℝ) = 1 := by exact_mod_cast ht.1
  have ht1 : ((1/5:ℚ):ℝ) < (adjointTrialCoefficient 1:ℝ) := Rat.cast_lt.mpr ht.2.1
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at ht1
  let f : Fin 18 → ℝ := fun j => (adjointTrialCoefficient j:ℝ)*
    (2*((j.val+1:ℕ):ℝ)*evenCoefficient thetaParameter nome (j.val+1))
  have hf (j : Fin 18) : 0 ≤ f j := by
    have htj : 0 ≤ (adjointTrialCoefficient j:ℝ) := by exact_mod_cast (ht.2.2 j).le
    have hcj : 0 ≤ evenCoefficient thetaParameter nome (j.val+1) := by
      simpa only [fourierCoefficient,if_neg (by omega : j.val+1 ≠ 0)] using
        (theta_nome_coefficient_majorant (j.val+1) (by omega)).1
    dsimp only [f]
    positivity
  have htwo : f 0+f 1 ≤ ∑ j : Fin 18, f j := by
    have hs := sum_le_sum_of_subset_of_nonneg
      (subset_univ ({0,1}:Finset (Fin 18))) (fun j _ _ => hf j)
    simpa only [sum_pair (by decide : (0:Fin 18) ≠ 1)] using hs
  have hpair : (51/100:ℝ) < ∑ j : Fin 18, f j := by
    have hprod := mul_le_mul_of_nonneg_right ht1.le (by linarith : 0 ≤ evenCoefficient thetaParameter nome 2)
    have hsmall : f 0+f 1 = 2*evenCoefficient thetaParameter nome 1+
        4*(adjointTrialCoefficient 1:ℝ)*evenCoefficient thetaParameter nome 2 := by
      dsimp only [f]
      rw [ht0]
      norm_num
      ring
    rw [hsmall] at htwo
    nlinarith only [hprod,h1',h2',htwo]
  unfold adjointTrialPairing
  apply (lt_div_iff₀ rotation_coefficient_norm_bounds.1).mpr
  simpa only [one_mul] using rotation_coefficient_norm_bounds.2.trans hpair

end Lemniscate.CoarseArithmetic
