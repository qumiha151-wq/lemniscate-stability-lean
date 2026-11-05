import Lemniscate.WeierstrassFrequencyBounds
import Lemniscate.RoundedIntervals
import Lemniscate.CoefficientMajorant

/-! Scalar and Fourier enclosures used by the seven-dimensional proof.
The scalar inputs follow from the previously proved bounds for the actual
nome and frequency. No finite Bloch certificate is imported. -/
namespace Lemniscate.CoarseArithmetic
open Finset

def shortFrequencyInterval : Interval :=
  ⟨7177700110/10^10,7177700111/10^10⟩

def shortNomeInterval : Interval :=
  ⟨4321391826/10^11,4321391827/10^11⟩

theorem short_frequency_enclosure :
    Contains shortFrequencyInterval lemniscateFrequencySquared :=
  lemniscate_frequency_bounds.mono
    (by norm_num [shortFrequencyInterval,frequencyLower])
    (by norm_num [shortFrequencyInterval,frequencyUpper])

theorem short_nome_enclosure : Contains shortNomeInterval nome :=
  refined_nome_bounds.mono
    (by norm_num [shortNomeInterval,nomeLower])
    (by norm_num [shortNomeInterval,nomeUpper])

def shortPositiveInterval (j : ℕ) : Interval := roundInterval 24
  ⟨8*shortFrequencyInterval.lo*(j:ℚ)*shortNomeInterval.lo^j/
      (1-shortNomeInterval.lo^(2*j)),
   8*shortFrequencyInterval.hi*(j:ℚ)*shortNomeInterval.hi^j/
      (1-shortNomeInterval.hi^(2*j))⟩

theorem short_positive_fourier_enclosure (j : ℕ) (hj : 0 < j) :
    Contains (shortPositiveInterval j)
      (evenCoefficient lemniscateFrequencySquared nome j) := by
  have hr := short_frequency_enclosure
  have hq := short_nome_enclosure
  have hr0 : 0 ≤ lemniscateFrequencySquared :=
    (by norm_num [shortFrequencyInterval] :
      (0:ℝ) ≤ (shortFrequencyInterval.lo:ℝ)).trans hr.1
  have hq0 : 0 ≤ nome := (Real.exp_pos _).le
  have hq1 : nome < 1 := hq.2.trans_lt (by norm_num [shortNomeInterval])
  have hl := evenCoefficient_mono (shortFrequencyInterval.lo:ℝ)
    lemniscateFrequencySquared (shortNomeInterval.lo:ℝ) nome j
    (by norm_num [shortFrequencyInterval]) hr.1
    (by norm_num [shortNomeInterval]) hq.1 hq1 hj
  have hu := evenCoefficient_mono lemniscateFrequencySquared
    (shortFrequencyInterval.hi:ℝ) nome (shortNomeInterval.hi:ℝ) j
    hr0 hr.2 hq0 hq.2 (by norm_num [shortNomeInterval]) hj
  apply roundInterval_sound
  constructor
  · simpa only [evenCoefficient,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,
      Rat.cast_natCast,Rat.cast_pow,Rat.cast_sub,Rat.cast_one] using hl
  · simpa only [evenCoefficient,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,
      Rat.cast_natCast,Rat.cast_pow,Rat.cast_sub,Rat.cast_one] using hu

def shortConstantInterval : Interval := roundInterval 24
  ⟨1-2*sumTo 40 (fun j => (shortPositiveInterval (j+1)).hi)-2*H*tail1 qb 41,
   1-2*sumTo 40 (fun j => (shortPositiveInterval (j+1)).lo)⟩

theorem short_constant_fourier_enclosure :
    Contains shortConstantInterval (constantCoefficient lemniscateFrequencySquared nome) := by
  have hq : Contains ⟨qlo,qhi⟩ nome := short_nome_enclosure.mono
    (by norm_num [qlo,shortNomeInterval]) (by norm_num [qhi,shortNomeInterval])
  have hr : Contains ⟨rlo,rhi⟩ lemniscateFrequencySquared :=
    short_frequency_enclosure.mono
      (by norm_num [rlo,shortFrequencyInterval]) (by norm_num [rhi,shortFrequencyInterval])
  have hs := summable_fourier_tail lemniscateFrequencySquared nome 1 hr hq (by decide)
  have hsplit := hs.sum_add_tsum_nat_add 40
  simp only [Nat.add_assoc] at hsplit
  have hlo : (sumTo 40 (fun j => (shortPositiveInterval (j+1)).lo):ℝ) ≤
      ∑ j ∈ range 40, evenCoefficient lemniscateFrequencySquared nome (j+1) := by
    rw [OddArithmetic.sumTo_eq_sum_range,Rat.cast_sum]
    exact sum_le_sum (fun j _ => (short_positive_fourier_enclosure (j+1) (by omega)).1)
  have hhi : (∑ j ∈ range 40, evenCoefficient lemniscateFrequencySquared nome (j+1)) ≤
      (sumTo 40 (fun j => (shortPositiveInterval (j+1)).hi):ℝ) := by
    rw [OddArithmetic.sumTo_eq_sum_range,Rat.cast_sum]
    exact sum_le_sum (fun j _ => (short_positive_fourier_enclosure (j+1) (by omega)).2)
  have htailS := summable_fourier_tail lemniscateFrequencySquared nome 41 hr hq (by decide)
  have hmajor (j : ℕ) : evenCoefficient lemniscateFrequencySquared nome (j+41) ≤
      (H:ℝ)*(((j+41:ℕ):ℝ)*(qb:ℝ)^(j+41)) := by
    simpa only [fourierCoefficient,if_neg (by omega : j+41 ≠ 0)] using
      (frequency_nome_coefficient_majorant (j+41) (by omega)).2
  have hgeom := (tail1_sound qb (by norm_num [qb,Real.norm_eq_abs]) 41).mul_left (H:ℝ)
  have ht := htailS.tsum_le_tsum hmajor hgeom.summable
  rw [hgeom.tsum_eq] at ht
  have ht0 : 0 ≤ ∑' j : ℕ, evenCoefficient lemniscateFrequencySquared nome (j+41) := by
    apply tsum_nonneg
    intro j
    simpa only [fourierCoefficient,if_neg (by omega : j+41 ≠ 0)] using
      (frequency_nome_coefficient_majorant (j+41) (by omega)).1
  apply roundInterval_sound
  change ((1-2*sumTo 40 (fun j => (shortPositiveInterval (j+1)).hi)-
    2*H*tail1 qb 41:ℚ):ℝ) ≤ constantCoefficient lemniscateFrequencySquared nome ∧
    constantCoefficient lemniscateFrequencySquared nome ≤
      ((1-2*sumTo 40 (fun j => (shortPositiveInterval (j+1)).lo):ℚ):ℝ)
  simp only [Rat.cast_sub,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,constantCoefficient]
  constructor <;> linarith only [hlo,hhi,hsplit,ht,ht0]

end Lemniscate.CoarseArithmetic
