import Lemniscate.PeriodicWeakSecond

/-! The weak second derivative is uniquely determined, and its test-function
definition is equivalent to the Fourier multiplier identity. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_continuous_l2_smul (c : ℂ) (f : C(AddCircle T, ℂ)) :
    circleContinuousL2 T (c • f) = c • circleContinuousL2 T f :=
  (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).map_smul c f

theorem circle_continuous_l2_fourier_basis (n : ℤ) :
    circleContinuousL2 T (fourier n) = fourierBasis (T := T) n := by
  change fourierLp (T := T) 2 n = fourierBasis (T := T) n
  exact (congrFun (coe_fourierBasis (T := T)) n).symm

theorem hasCircleDeriv_fourier (n : ℤ) :
    HasCircleDeriv T (fourier n) (circleFrequencyFactor T n • fourier n) := by
  intro x
  exact hasDerivAt_circle_fourier T n x

theorem hasCircleDeriv_fourier_first (n : ℤ) :
    HasCircleDeriv T (circleFrequencyFactor T n • fourier n)
      (((-((2*Real.pi/T)^2*(n:ℝ)^2):ℝ):ℂ) • fourier n) := by
  intro x
  change HasDerivAt (fun y : ℝ => circleFrequencyFactor T n * fourier n (y : AddCircle T))
    (((-((2*Real.pi/T)^2*(n:ℝ)^2):ℝ):ℂ) * fourier n (x : AddCircle T)) x
  convert! (hasDerivAt_circle_fourier T n x).const_mul (circleFrequencyFactor T n) using 1
  rw [← circle_frequency_factor_sq]
  ring

theorem fourier_of_weak_circle_second (f g : CircleL2 T) (hfg : HasWeakCircleSecond T f g)
    (n : ℤ) :
    fourierCoeff g n = ((-((2*Real.pi/T)^2*(n:ℝ)^2):ℝ):ℂ)*fourierCoeff f n := by
  have h := hfg (fourier n) (circleFrequencyFactor T n • fourier n)
    (((-((2*Real.pi/T)^2*(n:ℝ)^2):ℝ):ℂ) • fourier n)
    (hasCircleDeriv_fourier T n) (hasCircleDeriv_fourier_first T n)
  rw [circle_continuous_l2_fourier_basis, circle_continuous_l2_smul,
    circle_continuous_l2_fourier_basis, inner_smul_right] at h
  have hc := congrArg conj h
  simp only [map_mul, Complex.conj_ofReal, inner_conj_symm] at hc
  simpa only [← HilbertBasis.repr_apply_apply, fourierBasis_repr] using hc

theorem weak_circle_second_iff_fourier (f g : CircleL2 T) :
    HasWeakCircleSecond T f g ↔ ∀ n : ℤ, fourierCoeff g n =
      ((-((2*Real.pi/T)^2*(n:ℝ)^2):ℝ):ℂ)*fourierCoeff f n :=
  ⟨fourier_of_weak_circle_second T f g, weak_circle_second_of_fourier T f g⟩

theorem circle_fourier_ext (f g : CircleL2 T)
    (hfg : ∀ n : ℤ, fourierCoeff f n = fourierCoeff g n) : f = g := by
  apply (fourierBasis (T := T)).repr.injective
  ext n
  simpa only [fourierBasis_repr] using hfg n

theorem weak_circle_second_unique (f g h : CircleL2 T)
    (hfg : HasWeakCircleSecond T f g) (hfh : HasWeakCircleSecond T f h) : g = h := by
  apply circle_fourier_ext T
  intro n
  rw [fourier_of_weak_circle_second T f g hfg, fourier_of_weak_circle_second T f h hfh]

end Lemniscate
