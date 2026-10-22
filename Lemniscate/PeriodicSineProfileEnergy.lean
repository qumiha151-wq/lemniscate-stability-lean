import Lemniscate.PeriodicSineEnergy
import Lemniscate.PeriodicSineProfile
import Lemniscate.PeriodicProfileEnergy

/-! Restore the paper's curvature potential and the actual rotation vector.
The -75 bound now concerns the differential H2 energy. The particular Jacobi
profile's ODE, Fourier formula and period identity are still explicit hypotheses. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_profile_constraint (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (f : CircleL2 T) (horth : inner ℂ (circleContinuousL2 T (q*p)) f = 0) :
    inner ℂ (circleSineConstraintVector T) f = 0 := by
  have hcp (j : ℕ) (hj : 0 < j) :
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
        (evenCoefficient thetaParameter nome j:ℂ) := by
    simpa only [fourierCoefficient, if_neg (Nat.ne_of_gt hj)] using hc j
  exact (circle_sine_profile_rotation_orthogonal_iff T q p hq hs hcp ho f).mp horth

theorem paper_sine_weak_energy_dissipative (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter) (u : ℂ) (v : SineTailSpace)
    (f₁ f₂ : CircleL2 T) (hf : HasWeakCircleDeriv T (circleSineBlockFunction T u v) f₁)
    (hf₁ : HasWeakCircleDeriv T f₁ f₂)
    (horth : inner ℂ (circleContinuousL2 T (q*p)) (circleSineBlockFunction T u v) = 0) :
    paperH2Energy T q (circleSineBlockFunction T u v) f₁ f₂ ≤
      -75*‖circleSineBlockFunction T u v‖^2 := by
  rw [← circle_h2_energy_profile]
  exact circle_sine_weak_energy_dissipative T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
    (circle_profile_square_second T q p hq hp he) hs hc hr u v f₁ f₂ hf hf₁
    (circle_sine_profile_constraint T q p hq hs hc ho _ horth)

end Lemniscate
