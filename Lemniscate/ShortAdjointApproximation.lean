import Lemniscate.ShortSchurInputs
import Lemniscate.PeriodicSineAdjointTrial
import Lemniscate.PeriodicNeutralTransform

/-! The same common unit phase is used in the actual functions and in the
new seven-mode real antisymmetric Fourier matrices. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleShortRotationApproximation : circleH4Domain T :=
  I • circleSineTrialH4 T 7
    (fun j => (shortRotationSine shortActualCoefficient j:ℂ))

noncomputable def circleShortAdjointApproximation : circleH4Domain T :=
  I • circleSineTrialH4 T 7
    (fun j => (shortAdjointSine shortActualCoefficient j:ℂ))

noncomputable def circleShortRotationVector (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) : circleH4Domain T :=
  (-I) • circleUnitRotationH4 T q p hq hp

noncomputable def circleShortAdjointVector (ψ : circleH4Domain T) : circleH4Domain T :=
  (-I) • ψ

end Lemniscate
