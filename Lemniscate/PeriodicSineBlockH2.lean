import Lemniscate.PeriodicSineH2
import Lemniscate.PeriodicSineConstraint
import Lemniscate.PeriodicAdjointRegularity

/-! The first-mode/tail split has exactly the periodic H2 domain used by the
coefficient form. The energy below is still the coefficient-defined form;
its differential-expression identification is not assumed or asserted here. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

variable (T : ℝ) [Fact (0 < T)]

theorem circle_weak_second_add (f g u v : CircleL2 T)
    (hf : HasWeakCircleSecond T f g) (hu : HasWeakCircleSecond T u v) :
    HasWeakCircleSecond T (f+u) (g+v) := by
  intro φ φ₁ φ₂ h₁ h₂
  simp only [inner_add_left, hf φ φ₁ φ₂ h₁ h₂, hu φ φ₁ φ₂ h₁ h₂]

theorem circle_weak_second_smul (c : ℂ) (f g : CircleL2 T)
    (hf : HasWeakCircleSecond T f g) : HasWeakCircleSecond T (c • f) (c • g) := by
  intro φ φ₁ φ₂ h₁ h₂
  simp only [inner_smul_left, hf φ φ₁ φ₂ h₁ h₂]

theorem circle_sine_mode_weak_second (j : ℕ) :
    HasWeakCircleSecond T (circleEvenSineMode T j)
      (((-((2*Real.pi/T)^2*(2*((j:ℝ)+1))^2):ℝ):ℂ) • circleEvenSineMode T j) := by
  apply weak_circle_second_of_fourier
  intro n
  rw [circle_fourierCoeff_smul]
  calc
    _ = (((2*Real.pi/T)^2:ℝ):ℂ)*
        (((-(2*((j:ℝ)+1))^2:ℝ):ℂ)*fourierCoeff (circleEvenSineMode T j) n) := by
      push_cast
      ring
    _ = (((2*Real.pi/T)^2:ℝ):ℂ)*
        (((-(n:ℝ)^2:ℝ):ℂ)*fourierCoeff (circleEvenSineMode T j) n) := by
      rw [circle_sine_mode_second_multiplier]
    _ = _ := by push_cast; ring

theorem circle_sine_block_coeff_pos (u : ℂ) (v : SineTailSpace) (j : ℕ) :
    fourierCoeff (circleSineBlockFunction T u v) (2*((j+2:ℕ):ℤ)) = v j*evenSineFactor := by
  have h : fourierCoeff (circleEvenSineMode T 0) (2*((j+2:ℕ):ℤ)) = 0 := by
    have hj : (0:ℕ) ≠ j+1 := by omega
    simpa only [Nat.add_assoc, Nat.reduceAdd, hj, if_false] using
      circle_even_sine_mode_coeff_pos T (j+1) 0
  rw [circleSineBlockFunction, circle_fourierCoeff_add, circle_fourierCoeff_smul,
    h, mul_zero, zero_add, circle_sine_tail_coeff_pos]

theorem circle_sine_block_mem_h2_iff (u : ℂ) (v : SineTailSpace) :
    InCircleH2 T (circleSineBlockFunction T u v) ↔ HasSineTailH2Coefficients v := by
  rw [circle_h2_iff_weak_second]
  constructor
  · rintro ⟨g, hg⟩
    apply (sine_tail_h2_iff v).mpr
    exact circle_h2_sine_coefficients_of_positive T 2 (by decide) v _ g hg
      (circle_sine_block_coeff_pos T u v)
  · intro hv
    have ht := circle_sine_tail_weak_second T v ((sine_tail_h2_iff v).mp hv)
    have hf := circle_weak_second_smul T u _ _ (circle_sine_mode_weak_second T 0)
    exact ⟨_, circle_weak_second_add T _ _ _ _ hf ht⟩

theorem circle_sine_sobolev_constrained_coefficient_energy (u : ℂ) (v : SineTailSpace)
    (hv : InCircleH2 T (circleSineBlockFunction T u v))
    (horth : inner ℂ (circleSineConstraintVector T) (circleSineBlockFunction T u v) = 0) :
    sineH2BlockForm u v ≤ -75*‖circleSineBlockFunction T u v‖^2 :=
  circle_sine_constrained_coefficient_energy T u v
    ((circle_sine_block_mem_h2_iff T u v).mp hv) horth

end Lemniscate
