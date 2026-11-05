import Lemniscate.ShortAdjointResidualData
import Lemniscate.PeriodicBlochFourier

/-! Soundness of the new adjoint residual arithmetic. Every entry below uses
the actual frequency and nome and the proved Fourier coefficients. -/
namespace Lemniscate.CoarseArithmetic
open Finset

noncomputable def shortSineOperatorEntry (r q : ℝ) (i j : ℕ) : ℝ :=
  let n : ℝ := 2*i
  let m : ℝ := 2*j
  let v := r*(fourierCoefficient r q (i-j+(j-i))*(7*m-n)+
    fourierCoefficient r q (i+j)*(7*m+n))*((15/2:ℝ)*n)
  if i = j then v+(-4*r^2*n^4-42) else v

noncomputable def shortRawAdjointResidual (j : ℕ) : ℝ :=
  ∑ i : Fin 8, shortSineOperatorEntry lemniscateFrequencySquared nome (i.val+1) j *
    shortAdjointTrialCoeff i

theorem short_trial_rational_cast (i : Fin 8) :
    (shortTrialRationalCoeff i : ℝ) = shortAdjointTrialCoeff i := by
  simp only [shortTrialRationalCoeff, shortAdjointTrialCoeff,
    Rat.cast_div, Rat.cast_ofNat]

theorem short_h_interval_sound (j : ℕ) :
    Contains (shortHInterval j)
      (fourierCoefficient lemniscateFrequencySquared nome j) := by
  by_cases hj : j = 0
  · subst j
    simpa [shortHInterval, fourierCoefficient] using
      short_constant_fourier_enclosure
  · simpa only [shortHInterval, if_neg hj, fourierCoefficient, if_neg hj] using
      short_positive_fourier_enclosure j (Nat.pos_of_ne_zero hj)

theorem short_trial_sine_entry_sound (i : Fin 8) (j : Fin 16) :
    Contains (shortTrialSineEntry (i.val+1) (j.val+1))
      (shortSineOperatorEntry lemniscateFrequencySquared nome (i.val+1) (j.val+1)) := by
  have hr := short_frequency_enclosure
  have hm := scale_sound _ _ (7*(2*((j.val+1:ℕ):ℚ))-2*((i.val+1:ℕ):ℚ))
    (short_h_interval_sound (i.val+1-(j.val+1)+(j.val+1-(i.val+1))))
  have hp := scale_sound _ _ (7*(2*((j.val+1:ℕ):ℚ))+2*((i.val+1:ℕ):ℚ))
    (short_h_interval_sound (i.val+1+(j.val+1)))
  have hv := scale_sound _ _ ((15/2:ℚ)*(2*((i.val+1:ℕ):ℚ)))
    (mul_sound _ _ _ _ hr (add_sound _ _ _ _ hm hp))
  by_cases he : i.val+1 = j.val+1
  · have hr0 : 0 ≤ lemniscateFrequencySquared :=
      (by norm_num [shortFrequencyInterval] : (0:ℝ) ≤ (shortFrequencyInterval.lo:ℝ)).trans hr.1
    have hl := pow_le_pow_left₀
      (by norm_num [shortFrequencyInterval] : (0:ℝ) ≤ (shortFrequencyInterval.lo:ℝ)) hr.1 2
    have hu := pow_le_pow_left₀ hr0 hr.2 2
    have hd : Contains
        ⟨-4*shortFrequencyInterval.hi^2*(2*((i.val+1:ℕ):ℚ))^4-42,
          -4*shortFrequencyInterval.lo^2*(2*((i.val+1:ℕ):ℚ))^4-42⟩
        (-4*lemniscateFrequencySquared^2*(2*((i.val+1:ℕ):ℝ))^4-42) := by
      have hl' := mul_le_mul_of_nonneg_right hl
        (by positivity : (0:ℝ) ≤ (2*((i.val+1:ℕ):ℝ))^4)
      have hu' := mul_le_mul_of_nonneg_right hu
        (by positivity : (0:ℝ) ≤ (2*((i.val+1:ℕ):ℝ))^4)
      constructor <;> simp only [Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,
        Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast] <;> linarith
    simpa only [shortTrialSineEntry,shortSineOperatorEntry,if_pos he,
      Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sub,Rat.cast_add,
      Rat.cast_natCast] using add_sound _ _ _ _ hv hd
  · simpa only [shortTrialSineEntry,shortSineOperatorEntry,if_neg he,
      Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sub,Rat.cast_add,
      Rat.cast_natCast] using hv

theorem short_raw_residual_head_abs (j : Fin 16) :
    |shortRawAdjointResidual (j.val+1)| ≤ (absUpper (shortRawResidualInterval j):ℝ) := by
  have hs (i : Fin 8) := scale_sound _ _ (shortTrialRationalCoeff i)
    (short_trial_sine_entry_sound i j)
  have hh : Contains (shortRawResidualInterval j)
      (shortRawAdjointResidual (j.val+1)) := by
    constructor <;> simp only [shortRawResidualInterval, shortRawAdjointResidual,
      Rat.cast_sum, ← short_trial_rational_cast]
    · exact sum_le_sum fun i _ => (hs i).1
    · exact sum_le_sum fun i _ => (hs i).2
  exact absUpper_sound _ _ hh

theorem short_residual_weight_pos (j : ℕ) : 0 < (shortResidualWeight j:ℝ) := by
  simp only [shortResidualWeight, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast]
  positivity

theorem short_raw_residual_head_bound :
    (∑ j : Fin 16, (shortRawAdjointResidual (j.val+1))^2 /
      (shortResidualWeight (j.val+1):ℝ)) < (1/(5*10^10):ℝ) := by
  have hb : (∑ j : Fin 16, (shortRawAdjointResidual (j.val+1))^2 /
      (shortResidualWeight (j.val+1):ℝ)) ≤ (shortResidualHeadBound:ℝ) := by
    simp only [shortResidualHeadBound, Rat.cast_sum, Rat.cast_div, Rat.cast_pow]
    apply sum_le_sum
    intro j _
    have hsq := pow_le_pow_left₀ (abs_nonneg _) (short_raw_residual_head_abs j) 2
    rw [sq_abs] at hsq
    exact div_le_div_of_nonneg_right hsq (short_residual_weight_pos _).le
  have hc := (Rat.cast_lt (K := ℝ)).mpr short_residual_head_comparison
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] at hc
  have h := hb.trans_lt hc
  norm_num at h ⊢
  simpa using! h

theorem short_trial_sine_entry_tail (i : Fin 8) (j : ℕ) (hj : 17 ≤ j) :
    |shortSineOperatorEntry lemniscateFrequencySquared nome (i.val+1) j| ≤
      480*(rhi:ℝ)*(H:ℝ)*(j:ℝ)^3*(qb:ℝ)^(j-8) := by
  have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
  have hH : 0 ≤ (H:ℝ) := by norm_num [H,rhi,qb]
  have hr : Contains ⟨rlo,rhi⟩ lemniscateFrequencySquared :=
    short_frequency_enclosure.mono
      (by norm_num [rlo,shortFrequencyInterval])
      (by norm_num [rhi,shortFrequencyInterval])
  have hr0 : 0 ≤ lemniscateFrequencySquared :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans hr.1
  have hru : 0 ≤ (rhi:ℝ) := hr0.trans hr.2
  have hji : i.val+1 ≤ j := by omega
  have hij : i.val+1 ≠ j := by omega
  have hjr : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
  have hir : 0 ≤ ((i.val+1:ℕ):ℝ) := Nat.cast_nonneg _
  have hjir : ((i.val+1:ℕ):ℝ) ≤ (j:ℝ) := by exact_mod_cast hji
  let C : ℝ := (H:ℝ)*((j:ℝ)*(qb:ℝ)^(j-8))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcoeff (m : ℕ) (hm : j-8 ≤ m) :
      0 ≤ fourierCoefficient lemniscateFrequencySquared nome m ∧
        fourierCoefficient lemniscateFrequencySquared nome m ≤ C := by
    have hpos : 0 < j-8 := by omega
    have hp := (frequency_nome_coefficient_majorant m (hpos.trans_le hm)).1
    refine ⟨hp, ?_⟩
    calc
      _ ≤ |fourierCoefficient lemniscateFrequencySquared nome m| := le_abs_self _
      _ ≤ (H:ℝ)*(((j-8:ℕ):ℝ)*(qb:ℝ)^(j-8)) :=
        common_index_coefficient_majorant (j-8) m hpos hm
      _ ≤ C := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le j 8)
          (pow_nonneg hq _)) hH
  have hm := hcoeff (i.val+1-j+(j-(i.val+1))) (by omega)
  have hp := hcoeff (i.val+1+j) (by omega)
  have hm0 : 0 ≤ 7*(2*(j:ℝ))-2*((i.val+1:ℕ):ℝ) := by linarith
  have hp0 : 0 ≤ 7*(2*(j:ℝ))+2*((i.val+1:ℕ):ℝ) := by positivity
  have hmu : 7*(2*(j:ℝ))-2*((i.val+1:ℕ):ℝ) ≤ 16*(j:ℝ) := by linarith
  have hpu : 7*(2*(j:ℝ))+2*((i.val+1:ℕ):ℝ) ≤ 16*(j:ℝ) := by linarith
  have hprod := add_le_add
    (mul_le_mul hm.2 hmu hm0 hC) (mul_le_mul hp.2 hpu hp0 hC)
  have hs0 : 0 ≤
      fourierCoefficient lemniscateFrequencySquared nome (i.val+1-j+(j-(i.val+1)))*
        (7*(2*(j:ℝ))-2*((i.val+1:ℕ):ℝ))+
      fourierCoefficient lemniscateFrequencySquared nome (i.val+1+j)*
        (7*(2*(j:ℝ))+2*((i.val+1:ℕ):ℝ)) :=
    add_nonneg (mul_nonneg hm.1 hm0) (mul_nonneg hp.1 hp0)
  have houter := mul_le_mul hr.2 hprod hs0 hru
  have hfactor : (15/2:ℝ)*(2*((i.val+1:ℕ):ℝ)) ≤ 15*(j:ℝ) := by linarith
  have hfull := mul_le_mul houter hfactor (by positivity) (by positivity)
  have hn : 0 ≤ shortSineOperatorEntry lemniscateFrequencySquared nome (i.val+1) j := by
    simp only [shortSineOperatorEntry,if_neg hij]
    exact mul_nonneg (mul_nonneg hr0 hs0) (by positivity)
  rw [abs_of_nonneg hn]
  simp only [shortSineOperatorEntry,if_neg hij]
  refine hfull.trans_eq ?_
  dsimp only [C]
  ring

theorem short_raw_residual_tail_pointwise (j : ℕ) (hj : 17 ≤ j) :
    |shortRawAdjointResidual j| ≤
      (480*(rhi:ℝ)*(H:ℝ)*∑ i : Fin 8, shortAdjointTrialCoeff i)*
        (j:ℝ)^3*(qb:ℝ)^(j-8) := by
  have ht (i : Fin 8) : 0 ≤ shortAdjointTrialCoeff i := by
    rw [← short_trial_rational_cast]
    exact_mod_cast (short_trial_rational_positive.2.2 i).le
  unfold shortRawAdjointResidual
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i : Fin 8, (480*(rhi:ℝ)*(H:ℝ)*(j:ℝ)^3*(qb:ℝ)^(j-8))*
        shortAdjointTrialCoeff i := by
      apply sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (ht i)]
      exact mul_le_mul_of_nonneg_right (short_trial_sine_entry_tail i j hj) (ht i)
    _ = _ := by rw [← mul_sum]; ring

theorem short_raw_residual_weighted_tail :
    Summable (fun k : ℕ => (shortRawAdjointResidual (k+17))^2 /
      (shortResidualWeight (k+17):ℝ)) ∧
    (∑' k : ℕ, (shortRawAdjointResidual (k+17))^2 /
      (shortResidualWeight (k+17):ℝ)) ≤ (shortResidualTailBound:ℝ) := by
  let C : ℝ := 480*(rhi:ℝ)*(H:ℝ)*∑ i : Fin 8, shortAdjointTrialCoeff i
  let majorant : ℕ → ℝ := fun k => C^2/((52/25:ℝ)*(qb:ℝ)^16)*
    (((k+17:ℕ):ℝ)^2*((qb^2:ℚ):ℝ)^(k+17))
  have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
  have hqn : (qb:ℝ) ≠ 0 := by norm_num [qb]
  have hmajor0 (k : ℕ) : 0 ≤ majorant k := by
    dsimp only [majorant]
    positivity
  have hmajor (k : ℕ) : (shortRawAdjointResidual (k+17))^2 /
      (shortResidualWeight (k+17):ℝ) ≤ majorant k := by
    have hb := short_raw_residual_tail_pointwise (k+17) (by omega)
    have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hb2
    have hpow : ((qb:ℝ)^(k+17-8))^2 = ((qb:ℝ)^2)^(k+17)/(qb:ℝ)^16 := by
      rw [pow_sub₀ _ hqn (by omega),mul_pow,inv_pow,← pow_mul,← pow_mul]
      rw [Nat.mul_comm (k+17) 2]
      simp only [← pow_mul,Nat.reduceMul,div_eq_mul_inv]
    have heq : (C*((k+17:ℕ):ℝ)^3*(qb:ℝ)^(k+17-8))^2 =
        majorant k*((52/25:ℝ)*((k+17:ℕ):ℝ)^4) := by
      simp only [majorant,mul_pow,hpow,Rat.cast_pow,← pow_mul]
      field_simp
    have hw : (52/25:ℝ)*((k+17:ℕ):ℝ)^4 ≤
        (shortResidualWeight (k+17):ℝ) := by
      simp only [shortResidualWeight,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
        Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast]
      nlinarith
    apply (div_le_iff₀ (short_residual_weight_pos _)).mpr
    exact hb2.trans (heq.le.trans (mul_le_mul_of_nonneg_left hw (hmajor0 k)))
  have hsum := (moment_tail_sound 2 (by decide) (qb^2)
    (by norm_num [qb]) 17).mul_left (C^2/((52/25:ℝ)*(qb:ℝ)^16))
  have hs := Summable.of_nonneg_of_le
    (fun k => div_nonneg (sq_nonneg _) (short_residual_weight_pos _).le)
    hmajor hsum.summable
  refine ⟨hs, ?_⟩
  have ht := hs.tsum_le_tsum hmajor hsum.summable
  rw [hsum.tsum_eq] at ht
  refine ht.trans_eq ?_
  simp only [shortResidualTailBound,C,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,
    Rat.cast_ofNat,Rat.cast_sum,short_trial_rational_cast]
  ring

/-- The full weighted residual of the actual eight-mode coefficient trial,
including every infinite sine mode. -/
theorem short_raw_adjoint_residual_bound :
    Summable (fun j : ℕ => (shortRawAdjointResidual (j+1))^2 /
      (shortResidualWeight (j+1):ℝ)) ∧
    (∑' j : ℕ, (shortRawAdjointResidual (j+1))^2 /
      (shortResidualWeight (j+1):ℝ)) < (1/200000:ℝ)^2 := by
  let f : ℕ → ℝ := fun j => (shortRawAdjointResidual (j+1))^2 /
    (shortResidualWeight (j+1):ℝ)
  have htail : Summable (fun k : ℕ => f (k+16)) := by
    simpa only [f,Nat.add_assoc] using short_raw_residual_weighted_tail.1
  have hs : Summable f := (summable_nat_add_iff 16).mp htail
  refine ⟨hs, ?_⟩
  have hhead : (∑ j ∈ range 16, f j) < (1/(5*10^10):ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact short_raw_residual_head_bound
  have ht : (∑' k : ℕ, f (k+16)) < (1/(3*10^15):ℝ) := by
    have hc := (Rat.cast_lt (K := ℝ)).mpr short_residual_tail_comparison
    norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] at hc
    have h := short_raw_residual_weighted_tail.2.trans_lt hc
    norm_num [f,Nat.add_assoc]
    simpa using! h
  have hsplit := hs.sum_add_tsum_nat_add 16
  change (∑' j : ℕ, f j) < _
  linarith

end Lemniscate.CoarseArithmetic
