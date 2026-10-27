import Lemniscate.RawTrialArithmetic
import Lemniscate.PeriodicMatrixIdentification
import Lemniscate.PeriodicBlochFourier

/-! The full linearized operator in the sine basis, and soundness of the
finite rational intervals for its transposed action on the adjoint trial. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

namespace CoarseArithmetic

noncomputable def sineOperatorEntry (r q : ℝ) (i j : ℕ) : ℝ :=
  let n : ℝ := 2*(i:ℝ)
  let m : ℝ := 2*(j:ℝ)
  let v := r*(fourierCoefficient r q (i-j+(j-i))*(7*m-n)+
    fourierCoefficient r q (i+j)*(7*m+n))*((15/2:ℝ)*n)
  if i = j then v+(-4*r^2*n^4-42) else v

noncomputable def rawTrialResidual (j : ℕ) : ℝ :=
  ∑ i : Fin 18, sineOperatorEntry thetaParameter nome (i.val+1) j*
    (adjointTrialCoefficient i:ℝ)

theorem raw_trial_sine_entry_sound (i : Fin 18) (j : Fin 40) :
    Contains (rawTrialSineEntry (i.val+1) (j.val+1))
      (sineOperatorEntry thetaParameter nome (i.val+1) (j.val+1)) := by
  have hr : Contains ⟨thetaRLower,thetaRUpper⟩ thetaParameter := actual_nome_theta_r_bounds
  have hdiff : i.val+1-(j.val+1)+(j.val+1-(i.val+1)) < 59 := by omega
  have hsum : i.val+1+(j.val+1) < 59 := by omega
  have hm := scale_sound _ _ (7*(2*((j.val+1:ℕ):ℚ))-2*((i.val+1:ℕ):ℚ))
    (fine_coefficient_data_sound ⟨_,hdiff⟩)
  have hp := scale_sound _ _ (7*(2*((j.val+1:ℕ):ℚ))+2*((i.val+1:ℕ):ℚ))
    (fine_coefficient_data_sound ⟨_,hsum⟩)
  have hv := scale_sound _ _ ((15/2:ℚ)*(2*((i.val+1:ℕ):ℚ)))
    (mul_sound _ _ _ _ hr (add_sound _ _ _ _ hm hp))
  by_cases he : i.val+1 = j.val+1
  · have hr0 : 0 ≤ thetaParameter :=
      (by norm_num [thetaRLower] : (0:ℝ) ≤ (thetaRLower:ℝ)).trans hr.1
    have hl := pow_le_pow_left₀ (by norm_num [thetaRLower] : (0:ℝ) ≤ (thetaRLower:ℝ)) hr.1 2
    have hu := pow_le_pow_left₀ hr0 hr.2 2
    have hd : Contains
        ⟨-4*thetaRUpper^2*(2*((i.val+1:ℕ):ℚ))^4-42,
         -4*thetaRLower^2*(2*((i.val+1:ℕ):ℚ))^4-42⟩
        (-4*thetaParameter^2*(2*((i.val+1:ℕ):ℝ))^4-42) := by
      have hl' := mul_le_mul_of_nonneg_right hl
        (by positivity : (0:ℝ) ≤ (2*((i.val+1:ℕ):ℝ))^4)
      have hu' := mul_le_mul_of_nonneg_right hu
        (by positivity : (0:ℝ) ≤ (2*((i.val+1:ℕ):ℝ))^4)
      constructor <;> simp only [Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,
        Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast] <;> linarith
    simpa only [rawTrialSineEntry,sineOperatorEntry,if_pos he,
      Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sub,Rat.cast_add,
      Rat.cast_natCast] using add_sound _ _ _ _ hv hd
  · simpa only [rawTrialSineEntry,sineOperatorEntry,if_neg he,
      Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sub,Rat.cast_add,
      Rat.cast_natCast] using hv

theorem raw_trial_residual_head_bound (j : Fin 40) :
    |∑ i : Fin 18, sineOperatorEntry thetaParameter nome (i.val+1) (j.val+1)*
        (adjointTrialCoefficient i:ℝ)| ≤ (rawTrialResidualBound j:ℝ) := by
  have hs (i : Fin 18) := scale_sound _ _ (adjointTrialCoefficient i)
    (raw_trial_sine_entry_sound i j)
  have hh : Contains (rawTrialResidualInterval j)
      (∑ i : Fin 18, sineOperatorEntry thetaParameter nome (i.val+1) (j.val+1)*
        (adjointTrialCoefficient i:ℝ)) := by
    constructor <;> simp only [rawTrialResidualInterval,Rat.cast_sum]
    · exact Finset.sum_le_sum fun i _ => (hs i).1
    · exact Finset.sum_le_sum fun i _ => (hs i).2
  exact (absUpper_sound _ _ hh).trans (by exact_mod_cast raw_trial_residual_comparisons j)

end CoarseArithmetic

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_operator_entry (h : C(AddCircle T, ℂ)) (r q : ℝ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient r q j:ℂ))
    (hr : (2*Real.pi/T)^2 = r) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    circleBlochFourierEntry T h 0 (2*(i:ℤ)) (2*(j:ℤ))-
      circleBlochFourierEntry T h 0 (-(2*(i:ℤ))) (2*(j:ℤ)) =
        (sineOperatorEntry r q i j:ℂ) := by
  have hneg : -(2*(i:ℤ)) ≠ 2*(j:ℤ) := by omega
  have hpos : (2*(i:ℤ) = 2*(j:ℤ)) ↔ i = j := by omega
  have hfreq : -(2*(i:ℤ))-2*(j:ℤ) = -(2*(i:ℤ)+2*(j:ℤ)) := by ring
  have hr4 : (2*Real.pi/T)^4 = r^2 := by
    calc
      _ = ((2*Real.pi/T)^2)^2 := by ring
      _ = _ := by rw [hr]
  simp only [circleBlochFourierEntry,add_zero,if_neg hneg,hfreq,hs,
    circle_even_coefficient_difference T h r q hs hc,
    circle_even_coefficient_sum T h r q hc,hr,hr4,hpos,
    sineOperatorEntry]
  by_cases he : i = j
  · subst j
    simp only [if_pos rfl,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    push_cast
    ring
  · simp only [if_neg he,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    push_cast
    ring

end Lemniscate
