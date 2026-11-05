import Lemniscate.PeriodicBlochCenter
import Lemniscate.PeriodicBlochGreen
import Lemniscate.PeriodicReducedForm

/-! Exact symmetric and reduced forms, with no finite certificate dependency. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleExactSymmetricCoefficient (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : circleH4Domain T) (j : Fin 5) (f g : circleH4Domain T) : ℂ :=
  if j = 0 then
    inner ℂ (circleRotationHouseholderH4 T q p hq hp f:CircleL2 T)
      (circleH4SymmetricOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
        (circleRotationHouseholderH4 T q p hq hp g))
  else (1/2:ℂ)*(inner ℂ (f:CircleL2 T) (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) j g)+
    inner ℂ (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) j f) (g:CircleL2 T))

noncomputable def circleExactReducedBlochPairing (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : circleH4Domain T) (α : ℝ) (f g : circleH4Domain T) : ℂ :=
  circleReducedBlochForm T (circleExactSymmetricCoefficient T q p hq hp ψ) α f g

end Lemniscate
