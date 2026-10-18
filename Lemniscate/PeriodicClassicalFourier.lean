import Lemniscate.CosineModeDerivatives

/-! Fourier differentiation for classical periodic functions, including the
zero Fourier coefficient. Endpoint terms cancel on the circle. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

def HasCircleDeriv (f g : C(AddCircle T, ℂ)) : Prop :=
  ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle T)) (g (x : AddCircle T)) x

theorem circle_frequency_factor_neg (n : ℤ) :
    circleFrequencyFactor T (-n) = -circleFrequencyFactor T n := by
  simp [circleFrequencyFactor]

theorem fourierCoeff_classical_deriv (f g : C(AddCircle T, ℂ))
    (hfg : HasCircleDeriv T f g) (n : ℤ) :
    fourierCoeff g n = circleFrequencyFactor T n * fourierCoeff f n := by
  have hfI : IntervalIntegrable
      (fun x : ℝ => fourier (-n) (x : AddCircle T) * f (x : AddCircle T)) volume 0 T :=
    (((fourier (-n)).continuous.comp (AddCircle.continuous_mk' T)).mul
      (f.continuous.comp (AddCircle.continuous_mk' T))).intervalIntegrable 0 T
  have hgI : IntervalIntegrable
      (fun x : ℝ => fourier (-n) (x : AddCircle T) * g (x : AddCircle T)) volume 0 T :=
    (((fourier (-n)).continuous.comp (AddCircle.continuous_mk' T)).mul
      (g.continuous.comp (AddCircle.continuous_mk' T))).intervalIntegrable 0 T
  have hp : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => fourier (-n) (y : AddCircle T) * f (y : AddCircle T))
      (fourier (-n) (x : AddCircle T) * g (x : AddCircle T) -
        circleFrequencyFactor T n * (fourier (-n) (x : AddCircle T) * f (x : AddCircle T))) x := by
    intro x
    convert! (hasDerivAt_circle_fourier T (-n) x).mul (hfg x) using 1
    rw [circle_frequency_factor_neg]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hp x) (hgI.sub (hfI.const_mul (circleFrequencyFactor T n)))
  have hz : (∫ x : ℝ in 0..T,
      (fourier (-n) (x : AddCircle T) * g (x : AddCircle T) -
        circleFrequencyFactor T n * (fourier (-n) (x : AddCircle T) * f (x : AddCircle T)))) = 0 := by
    simpa only [AddCircle.coe_period, AddCircle.coe_zero, sub_self] using hi
  rw [intervalIntegral.integral_sub hgI (hfI.const_mul (circleFrequencyFactor T n)),
    intervalIntegral.integral_const_mul] at hz
  have heq := sub_eq_zero.mp hz
  rw [fourierCoeff_eq_intervalIntegral g n 0, fourierCoeff_eq_intervalIntegral f n 0]
  simp only [zero_add, smul_eq_mul, real_smul]
  rw [heq]
  ring

theorem fourierCoeff_classical_second (f g h : C(AddCircle T, ℂ))
    (hfg : HasCircleDeriv T f g) (hgh : HasCircleDeriv T g h) (n : ℤ) :
    fourierCoeff h n = ((-((2*Real.pi/T)^2*(n:ℝ)^2):ℝ):ℂ) * fourierCoeff f n := by
  rw [fourierCoeff_classical_deriv T g h hgh, fourierCoeff_classical_deriv T f g hfg]
  rw [← mul_assoc, ← pow_two, circle_frequency_factor_sq]

end Lemniscate
