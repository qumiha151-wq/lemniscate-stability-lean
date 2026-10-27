import Lemniscate.PeriodicH2Fourier
import Lemniscate.PeriodicDerivativeGraph
import Lemniscate.OddH2Dissipation

/-! The odd Fourier sector of the actual circle L2 space, its complete
reconstruction and Parseval identity, and its H2 coefficient regularity. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic OddArithmetic

theorem odd_frequency_injective : Function.Injective (fun i : ℤ => 2*i+1) := by
  intro i j hij
  change 2*i+1 = 2*j+1 at hij
  omega

theorem odd_frequency_range (n : ℤ) : n ∈ Set.range (fun i : ℤ => 2*i+1) ↔ Odd n := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by ring⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change 2*i+1 = n
    omega

theorem odd_frequency_hasSum_iff {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (a : ℤ → E) (b : E) (ha : ∀ n : ℤ, ¬Odd n → a n = 0) :
    HasSum (fun i : ℤ => a (2*i+1)) b ↔ HasSum a b := by
  apply odd_frequency_injective.hasSum_iff
  intro n hn
  exact ha n (fun ho => hn ((odd_frequency_range n).mpr ho))

variable (T : ℝ) [Fact (0 < T)]

def InCircleOddSector (f : CircleL2 T) : Prop :=
  ∀ n : ℤ, ¬Odd n → fourierCoeff f n = 0

theorem circle_odd_sector_weak_deriv (f g : CircleL2 T)
    (hf : InCircleOddSector T f) (hfg : HasWeakCircleDeriv T f g) :
    InCircleOddSector T g := by
  intro n hn
  rw [fourier_of_weak_circle_deriv T f g hfg, hf n hn, mul_zero]

theorem circle_odd_fourier_hasSum (f : CircleL2 T) (hf : InCircleOddSector T f) :
    HasSum (fun i : ℤ => fourierCoeff f (2*i+1) • fourierBasis (T := T) (2*i+1)) f := by
  apply (odd_frequency_hasSum_iff
    (fun n => fourierCoeff f n • fourierBasis (T := T) n) f ?_).mpr
  · simpa only [fourierBasis_repr] using (fourierBasis (T := T)).hasSum_repr f
  · intro n hn
    rw [hf n hn, zero_smul]

theorem circle_odd_norm_sq (f : CircleL2 T) (hf : InCircleOddSector T f) :
    ‖f‖^2 = ∑' i : ℤ, ‖fourierCoeff f (2*i+1)‖^2 := by
  have hs : HasSum (fun n : ℤ => ‖fourierCoeff f n‖^2) (‖f‖^2) := by
    rw [circle_norm_sq_fourier]
    exact (circle_fourier_square_summable T f).hasSum
  exact ((odd_frequency_hasSum_iff _ _ (fun n hn => by rw [hf n hn]; simp)).mpr hs).tsum_eq.symm

theorem circle_odd_h2_coefficients (f : CircleL2 T) (hf : InCircleH2 T f)
    (hr : (2*Real.pi/T)^2 = thetaParameter) :
    HasOddH2Coefficients (fun i : ℤ => fourierCoeff f (2*i+1)) := by
  have htheta : (1/2:ℝ) ≤ thetaParameter := by
    have hb : (rlo:ℝ) ≤ thetaParameter := (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1
    norm_num [rlo] at hb
    linarith
  have hw (n : ℝ) : 1+n^2 ≤ 2*(1+(2*Real.pi/T*n)^2) := by
    rw [mul_pow, hr]
    nlinarith [mul_nonneg (sub_nonneg.mpr htheta) (sq_nonneg n)]
  have hs := ((circle_h2_iff_weighted_fourier T f).mp hf).comp_injective odd_frequency_injective
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hs.mul_left 4)
  intro i
  have hb := mul_le_mul_of_nonneg_right (hw ((2*i+1:ℤ):ℝ))
    (norm_nonneg (fourierCoeff f (2*i+1)))
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤
    (1+(((2*i+1:ℤ):ℝ))^2)*‖fourierCoeff f (2*i+1)‖) hb 2
  simpa only [oddFrequencyWeight, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one,
    Function.comp_def, mul_pow, mul_assoc, show (2:ℝ)^2 = 4 by norm_num] using hp

end Lemniscate
