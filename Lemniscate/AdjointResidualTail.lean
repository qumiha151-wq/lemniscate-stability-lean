import Lemniscate.AdjointResidualEntries
import Lemniscate.CoefficientMajorant

/-! The complete infinite residual tail; no truncation is substituted for
the adjoint differential operator. -/
namespace Lemniscate.CoarseArithmetic
open Finset

theorem raw_trial_sine_entry_tail (i : Fin 18) (j : ℕ) (hj : 41 ≤ j) :
    |sineOperatorEntry thetaParameter nome (i.val+1) j| ≤
      480*(rhi:ℝ)*(H:ℝ)*(j:ℝ)^3*(qb:ℝ)^(j-18) := by
  have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
  have hH : 0 ≤ (H:ℝ) := by norm_num [H,rhi,qb]
  have hr : Contains ⟨rlo,rhi⟩ thetaParameter := actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩)
    (by norm_num [rlo,thetaRLower]) (by norm_num [rhi,thetaRUpper])
  have hr0 : 0 ≤ thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans hr.1
  have hru : 0 ≤ (rhi:ℝ) := hr0.trans hr.2
  have hji : i.val+1 ≤ j := by omega
  have hij : i.val+1 ≠ j := by omega
  have hjr : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
  have hir : 0 ≤ ((i.val+1:ℕ):ℝ) := Nat.cast_nonneg _
  have hjir : ((i.val+1:ℕ):ℝ) ≤ (j:ℝ) := by exact_mod_cast hji
  let C : ℝ := (H:ℝ)*((j:ℝ)*(qb:ℝ)^(j-18))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcoeff (m : ℕ) (hm : j-18 ≤ m) :
      0 ≤ fourierCoefficient thetaParameter nome m ∧
        fourierCoefficient thetaParameter nome m ≤ C := by
    have hpos : 0 < j-18 := by omega
    have hp := (theta_nome_coefficient_majorant m (hpos.trans_le hm)).1
    refine ⟨hp, ?_⟩
    calc
      _ ≤ |fourierCoefficient thetaParameter nome m| := le_abs_self _
      _ ≤ (H:ℝ)*(((j-18:ℕ):ℝ)*(qb:ℝ)^(j-18)) :=
        common_index_coefficient_majorant (j-18) m hpos hm
      _ ≤ C := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le j 18)
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
      fourierCoefficient thetaParameter nome (i.val+1-j+(j-(i.val+1)))*
        (7*(2*(j:ℝ))-2*((i.val+1:ℕ):ℝ))+
      fourierCoefficient thetaParameter nome (i.val+1+j)*
        (7*(2*(j:ℝ))+2*((i.val+1:ℕ):ℝ)) :=
    add_nonneg (mul_nonneg hm.1 hm0) (mul_nonneg hp.1 hp0)
  have houter := mul_le_mul hr.2 hprod hs0 hru
  have hfactor : (15/2:ℝ)*(2*((i.val+1:ℕ):ℝ)) ≤ 15*(j:ℝ) := by linarith
  have hfull := mul_le_mul houter hfactor (by positivity) (by positivity)
  have hn : 0 ≤ sineOperatorEntry thetaParameter nome (i.val+1) j := by
    simp only [sineOperatorEntry,if_neg hij]
    exact mul_nonneg (mul_nonneg hr0 hs0) (by positivity)
  rw [abs_of_nonneg hn]
  simp only [sineOperatorEntry,if_neg hij]
  refine hfull.trans_eq ?_
  dsimp only [C]
  ring

theorem raw_trial_residual_tail_pointwise (j : ℕ) (hj : 41 ≤ j) :
    |rawTrialResidual j| ≤
      (480*(rhi:ℝ)*(H:ℝ)*∑ i : Fin 18, (adjointTrialCoefficient i:ℝ))*
        (j:ℝ)^3*(qb:ℝ)^(j-18) := by
  have ht (i : Fin 18) : 0 ≤ (adjointTrialCoefficient i:ℝ) := by
    exact_mod_cast (adjoint_trial_coefficient_bounds.2.2 i).le
  unfold rawTrialResidual
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i : Fin 18, (480*(rhi:ℝ)*(H:ℝ)*(j:ℝ)^3*(qb:ℝ)^(j-18))*
        (adjointTrialCoefficient i:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (ht i)]
      exact mul_le_mul_of_nonneg_right (raw_trial_sine_entry_tail i j hj) (ht i)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem raw_trial_residual_tail_bound :
    Summable (fun k : ℕ => (rawTrialResidual (k+41))^2) ∧
      (∑' k : ℕ, (rawTrialResidual (k+41))^2) ≤ (rawTrialTailBound:ℝ) := by
  let C : ℝ := 480*(rhi:ℝ)*(H:ℝ)*∑ i : Fin 18, (adjointTrialCoefficient i:ℝ)
  let majorant : ℕ → ℝ := fun k => C^2/(qb:ℝ)^36*
    (((k+41:ℕ):ℝ)^6*((qb^2:ℚ):ℝ)^(k+41))
  have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
  have hqn : (qb:ℝ) ≠ 0 := by norm_num [qb]
  have hC : 0 ≤ C := by
    have ht (i : Fin 18) : 0 ≤ (adjointTrialCoefficient i:ℝ) := by
      exact_mod_cast (adjoint_trial_coefficient_bounds.2.2 i).le
    have hs : 0 ≤ ∑ i : Fin 18, (adjointTrialCoefficient i:ℝ) :=
      Finset.sum_nonneg fun i _ => ht i
    have hr : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
    have hH : 0 ≤ (H:ℝ) := by norm_num [H,rhi,qb]
    dsimp only [C]
    positivity
  have hmajor (k : ℕ) : (rawTrialResidual (k+41))^2 ≤ majorant k := by
    have hb := raw_trial_residual_tail_pointwise (k+41) (by omega)
    have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hb2
    refine hb2.trans_eq ?_
    have hpow : ((qb:ℝ)^(k+41-18))^2 = ((qb:ℝ)^2)^(k+41)/(qb:ℝ)^36 := by
      rw [pow_sub₀ _ hqn (by omega),mul_pow,inv_pow,← pow_mul,← pow_mul]
      rw [Nat.mul_comm (k+41) 2]
      simp only [← pow_mul,Nat.reduceMul,div_eq_mul_inv]
    change (C*((k+41:ℕ):ℝ)^3*(qb:ℝ)^(k+41-18))^2 = _
    simp only [majorant,mul_pow,hpow,Rat.cast_pow,← pow_mul]
    ring
  have hsum := (moment_tail_sound 6 (by decide) (qb^2)
    (by norm_num [qb]) 41).mul_left (C^2/(qb:ℝ)^36)
  have hs := Summable.of_nonneg_of_le (fun k => sq_nonneg _) hmajor hsum.summable
  refine ⟨hs, ?_⟩
  have ht := hs.tsum_le_tsum hmajor hsum.summable
  rw [hsum.tsum_eq] at ht
  refine ht.trans_eq ?_
  simp only [rawTrialTailBound,C,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,
    Rat.cast_ofNat,Rat.cast_sum]
  ring

end Lemniscate.CoarseArithmetic
