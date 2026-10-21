import Lemniscate.PeriodicSineRotation

/-! Express the sine constraint using the actual rotation profile q*q'. The
Jacobi Fourier hypotheses remain explicit; the coefficient energy has not yet
been identified with the differential energy. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_profile_rotation_orthogonal_iff (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) = fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, 0 < j → fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (evenCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0) (f : CircleL2 T) :
    inner ℂ (circleContinuousL2 T (q*p)) f = 0 ↔
      inner ℂ (circleSineConstraintVector T) f = 0 := by
  have h := circle_sine_rotation_orthogonal_iff T (q^2) ((2:ℂ) • (q*p))
    (circle_profile_square_deriv T q p hq) hs hc ho f
  rw [circle_continuous_l2_smul, inner_smul_left] at h
  simpa using h

theorem paper_sine_sobolev_constrained_coefficient_energy (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) = fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, 0 < j → fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (evenCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (u : ℂ) (v : SineTailSpace)
    (hv : InCircleH2 T (circleSineBlockFunction T u v))
    (horth : inner ℂ (circleContinuousL2 T (q*p)) (circleSineBlockFunction T u v) = 0) :
    sineH2BlockForm u v ≤ -75*‖circleSineBlockFunction T u v‖^2 :=
  circle_sine_sobolev_constrained_coefficient_energy T u v hv
    ((circle_sine_profile_rotation_orthogonal_iff T q p hq hs hc ho _).mp horth)

end Lemniscate
