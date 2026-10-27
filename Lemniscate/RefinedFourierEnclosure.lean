import Lemniscate.ThetaBounds
import Lemniscate.RoundedIntervals
import Lemniscate.CoefficientMajorant

/-! Fine coefficient intervals for the fixed adjoint trial. The constant
coefficient includes every term beyond the finite sum. -/
namespace Lemniscate.CoarseArithmetic
open Finset

def refinedPositiveInterval (j : ℕ) : Interval := roundInterval 30
  ⟨8*thetaRLower*(j:ℚ)*nomeLower^j/(1-nomeLower^(2*j)),
   8*thetaRUpper*(j:ℚ)*nomeUpper^j/(1-nomeUpper^(2*j))⟩

theorem refined_positive_fourier_enclosure (j : ℕ) (hj : 0 < j) :
    Contains (refinedPositiveInterval j) (evenCoefficient thetaParameter nome j) := by
  have hr : Contains ⟨thetaRLower,thetaRUpper⟩ thetaParameter := actual_nome_theta_r_bounds
  have hq : Contains ⟨nomeLower,nomeUpper⟩ nome := refined_nome_bounds
  have hr0 : 0 ≤ thetaParameter :=
    (by norm_num [thetaRLower] : (0:ℝ) ≤ (thetaRLower:ℝ)).trans hr.1
  have hq0 : 0 ≤ nome := (Real.exp_pos _).le
  have hq1 : nome < 1 := hq.2.trans_lt (by norm_num [nomeUpper])
  have hl := evenCoefficient_mono (thetaRLower:ℝ) thetaParameter
    (nomeLower:ℝ) nome j (by norm_num [thetaRLower]) hr.1
    (by norm_num [nomeLower]) hq.1 hq1 hj
  have hu := evenCoefficient_mono thetaParameter (thetaRUpper:ℝ)
    nome (nomeUpper:ℝ) j hr0 hr.2 hq0 hq.2 (by norm_num [nomeUpper]) hj
  apply roundInterval_sound
  constructor
  · simpa only [evenCoefficient,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,
      Rat.cast_natCast,Rat.cast_pow,Rat.cast_sub,Rat.cast_one] using hl
  · simpa only [evenCoefficient,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,
      Rat.cast_natCast,Rat.cast_pow,Rat.cast_sub,Rat.cast_one] using hu

def refinedConstantInterval : Interval := roundInterval 30
  ⟨1-2*sumTo 40 (fun j => (refinedPositiveInterval (j+1)).hi)-2*H*tail1 qb 41,
   1-2*sumTo 40 (fun j => (refinedPositiveInterval (j+1)).lo)⟩

theorem refined_constant_fourier_enclosure :
    Contains refinedConstantInterval (constantCoefficient thetaParameter nome) := by
  have hq : Contains ⟨qlo,qhi⟩ nome := refined_nome_bounds.mono
    (by norm_num [qlo,nomeLower]) (by norm_num [qhi,nomeUpper])
  have hs := summable_fourier_tail thetaParameter nome 1 (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo,thetaRLower]) (by norm_num [rhi,thetaRUpper])) hq (by decide)
  have hsplit := hs.sum_add_tsum_nat_add 40
  simp only [Nat.add_assoc] at hsplit
  have hlo : (sumTo 40 (fun j => (refinedPositiveInterval (j+1)).lo):ℝ) ≤
      ∑ j ∈ range 40, evenCoefficient thetaParameter nome (j+1) := by
    rw [OddArithmetic.sumTo_eq_sum_range,Rat.cast_sum]
    exact sum_le_sum (fun j _ => (refined_positive_fourier_enclosure (j+1) (by omega)).1)
  have hhi : (∑ j ∈ range 40, evenCoefficient thetaParameter nome (j+1)) ≤
      (sumTo 40 (fun j => (refinedPositiveInterval (j+1)).hi):ℝ) := by
    rw [OddArithmetic.sumTo_eq_sum_range,Rat.cast_sum]
    exact sum_le_sum (fun j _ => (refined_positive_fourier_enclosure (j+1) (by omega)).2)
  have htailS := summable_fourier_tail thetaParameter nome 41 (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo,thetaRLower]) (by norm_num [rhi,thetaRUpper])) hq (by decide)
  have hmajor (j : ℕ) : evenCoefficient thetaParameter nome (j+41) ≤
      (H:ℝ)*(((j+41:ℕ):ℝ)*(qb:ℝ)^(j+41)) := by
    simpa only [fourierCoefficient,if_neg (by omega : j+41 ≠ 0)] using
      (theta_nome_coefficient_majorant (j+41) (by omega)).2
  have hgeom := (tail1_sound qb (by norm_num [qb,Real.norm_eq_abs]) 41).mul_left (H:ℝ)
  have ht := htailS.tsum_le_tsum hmajor hgeom.summable
  rw [hgeom.tsum_eq] at ht
  have ht0 : 0 ≤ ∑' j : ℕ, evenCoefficient thetaParameter nome (j+41) := by
    apply tsum_nonneg
    intro j
    simpa only [fourierCoefficient,if_neg (by omega : j+41 ≠ 0)] using
      (theta_nome_coefficient_majorant (j+41) (by omega)).1
  apply roundInterval_sound
  change ((1-2*sumTo 40 (fun j => (refinedPositiveInterval (j+1)).hi)-
    2*H*tail1 qb 41:ℚ):ℝ) ≤ constantCoefficient thetaParameter nome ∧
    constantCoefficient thetaParameter nome ≤
      ((1-2*sumTo 40 (fun j => (refinedPositiveInterval (j+1)).lo):ℚ):ℝ)
  simp only [Rat.cast_sub,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,constantCoefficient]
  constructor <;> linarith only [hlo,hhi,hsplit,ht,ht0]

end Lemniscate.CoarseArithmetic
