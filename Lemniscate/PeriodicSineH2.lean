import Lemniscate.PeriodicSineTailCoefficients
import Lemniscate.SineSecondCoefficients
import Lemniscate.PeriodicH2Fourier
import Lemniscate.SineSobolevEntries

/-! Identify the full sine and tail coefficient domains with two actual weak
derivatives on the periodic circle. The coordinate scale 2*pi/T is explicit. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_mode_second_multiplier (j : ℕ) (n : ℤ) :
    ((-(2*((j:ℝ)+1))^2 : ℝ):ℂ)*fourierCoeff (circleEvenSineMode T j) n =
      ((-(n:ℝ)^2 : ℝ):ℂ)*fourierCoeff (circleEvenSineMode T j) n := by
  rw [circle_even_sine_mode_coeff]
  by_cases hp : n = 2*((j+1:ℕ):ℤ)
  · subst n
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
      Int.cast_add, Int.cast_one]
  · by_cases hn : n = -(2*((j+1:ℕ):ℤ))
    · subst n
      simp only [Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
        Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one, neg_sq]
    · simp only [hp, hn, if_false, sub_self, mul_zero]

theorem circle_sine_second_fourier (v : SineSequenceSpace)
    (hv : HasH2Coefficients (fun j => v j)) (n : ℤ) :
    fourierCoeff (circleEvenSineSynthesis T (sineSecondSequence 1 v hv)) n =
      ((-(n:ℝ)^2 : ℝ):ℂ)*fourierCoeff (circleEvenSineSynthesis T v) n := by
  have h := (circle_even_sine_coeff_hasSum T v n).mul_left (((-(n:ℝ)^2:ℝ):ℂ))
  apply (circle_even_sine_coeff_hasSum T (sineSecondSequence 1 v hv) n).unique
  convert! h using 1
  ext j
  change sineSecondCoefficients 1 v j*fourierCoeff (circleEvenSineMode T j) n = _
  calc
    _ = v j*((( -(2*((j:ℝ)+1))^2:ℝ):ℂ)*fourierCoeff (circleEvenSineMode T j) n) := by
      simp only [sineSecondCoefficients, Nat.cast_one]
      ring
    _ = v j*(((-(n:ℝ)^2:ℝ):ℂ)*fourierCoeff (circleEvenSineMode T j) n) := by
      rw [circle_sine_mode_second_multiplier]
    _ = _ := by ring

theorem circle_sine_tail_second_fourier (v : SineTailSpace)
    (hv : HasH2Coefficients (fun j => v j)) (n : ℤ) :
    fourierCoeff (circleSineTailSynthesis T (sineSecondSequence 2 v hv)) n =
      ((-(n:ℝ)^2 : ℝ):ℂ)*fourierCoeff (circleSineTailSynthesis T v) n := by
  have h := (circle_sine_tail_coeff_hasSum T v n).mul_left (((-(n:ℝ)^2:ℝ):ℂ))
  apply (circle_sine_tail_coeff_hasSum T (sineSecondSequence 2 v hv) n).unique
  convert! h using 1
  ext j
  change sineSecondCoefficients 2 v j*fourierCoeff (circleEvenSineMode T (j+1)) n = _
  calc
    _ = v j*((( -(2*(((j+1:ℕ):ℝ)+1))^2:ℝ):ℂ)*
        fourierCoeff (circleEvenSineMode T (j+1)) n) := by
      simp only [sineSecondCoefficients, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring
    _ = v j*(((-(n:ℝ)^2:ℝ):ℂ)*fourierCoeff (circleEvenSineMode T (j+1)) n) := by
      rw [circle_sine_mode_second_multiplier]
    _ = _ := by ring

theorem circle_sine_weak_second (v : SineSequenceSpace)
    (hv : HasH2Coefficients (fun j => v j)) :
    HasWeakCircleSecond T (circleEvenSineSynthesis T v)
      ((((2*Real.pi/T)^2:ℝ):ℂ) • circleEvenSineSynthesis T (sineSecondSequence 1 v hv)) := by
  apply weak_circle_second_of_fourier
  intro n
  rw [circle_fourierCoeff_smul, circle_sine_second_fourier]
  push_cast
  ring

theorem circle_sine_tail_weak_second (v : SineTailSpace)
    (hv : HasH2Coefficients (fun j => v j)) :
    HasWeakCircleSecond T (circleSineTailSynthesis T v)
      ((((2*Real.pi/T)^2:ℝ):ℂ) • circleSineTailSynthesis T (sineSecondSequence 2 v hv)) := by
  apply weak_circle_second_of_fourier
  intro n
  rw [circle_fourierCoeff_smul, circle_sine_tail_second_fourier]
  push_cast
  ring

theorem circle_h2_sine_coefficients_of_positive (offset : ℕ) (hoff : 0 < offset)
    (v : ℕ → ℂ) (f g : CircleL2 T) (hfg : HasWeakCircleSecond T f g)
    (hcoeff : ∀ j : ℕ, fourierCoeff f (2*((j+offset:ℕ):ℤ)) = v j*evenSineFactor) :
    HasH2Coefficients v := by
  apply (h2_iff_sine_second_l2 offset hoff v).mpr
  have hi : Function.Injective (fun j : ℕ => 2*((j+offset:ℕ):ℤ)) := by
    intro a b h
    change 2*((a+offset:ℕ):ℤ) = 2*((b+offset:ℕ):ℤ) at h
    omega
  have hs := (circle_fourier_square_summable T g).comp_injective hi
  have hm : Memℓp (fun j : ℕ => fourierCoeff g (2*((j+offset:ℕ):ℤ))) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Function.comp_def] using hs
  let d : ℂ := (((2*Real.pi/T)^2:ℝ):ℂ)*evenSineFactor
  have hd : d ≠ 0 := by
    apply mul_ne_zero _ evenSineFactor_ne_zero
    have hk : (2*Real.pi/T)^2 ≠ 0 := pow_ne_zero 2
      (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (ne_of_gt (Fact.out : 0 < T)))
    exact_mod_cast hk
  have hg (j : ℕ) : fourierCoeff g (2*((j+offset:ℕ):ℤ)) =
      d*sineSecondCoefficients offset v j := by
    rw [fourier_of_weak_circle_second T f g hfg, hcoeff]
    dsimp only [d, sineSecondCoefficients]
    push_cast
    ring
  have hm' := hm.const_mul d⁻¹
  have heq : (fun j : ℕ => d⁻¹*fourierCoeff g (2*((j+offset:ℕ):ℤ))) =
      sineSecondCoefficients offset v := by
    funext j
    rw [hg, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  rw [heq] at hm'
  exact hm'

theorem circle_sine_mem_h2_iff (v : SineSequenceSpace) :
    InCircleH2 T (circleEvenSineSynthesis T v) ↔ HasH2Coefficients (fun j => v j) := by
  rw [circle_h2_iff_weak_second]
  constructor
  · rintro ⟨g, hg⟩
    exact circle_h2_sine_coefficients_of_positive T 1 (by decide) v _ g hg
      (circle_even_sine_coeff_pos T v)
  · intro hv
    exact ⟨_, circle_sine_weak_second T v hv⟩

theorem circle_sine_tail_mem_h2_iff (v : SineTailSpace) :
    InCircleH2 T (circleSineTailSynthesis T v) ↔ HasSineTailH2Coefficients v := by
  rw [sine_tail_h2_iff, circle_h2_iff_weak_second]
  constructor
  · rintro ⟨g, hg⟩
    exact circle_h2_sine_coefficients_of_positive T 2 (by decide) v _ g hg
      (circle_sine_tail_coeff_pos T v)
  · intro hv
    exact ⟨_, circle_sine_tail_weak_second T v hv⟩

end Lemniscate
