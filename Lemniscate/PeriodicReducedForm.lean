import Lemniscate.PeriodicFixedProjection

/-! The exact reduced polynomial after cancellation of neutral factors. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleReducedBlochForm
    (H : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (α : ℝ) (f g : circleH4Domain T) : ℂ :=
  let f₀ := circleFixedProjectionH4 T f
  let g₀ := circleFixedProjectionH4 T g
  let f₁ := f-f₀
  let g₁ := g-g₀
  let c : ℂ := ((-4*(2*Real.pi/T)^4:ℝ):ℂ)
  H 2 f₀ g₀+c*(α:ℂ)^2*inner ℂ (f₀:CircleL2 T) (g₀:CircleL2 T)+
    (H 1 f₀ g₁+H 1 f₁ g₀)+(α:ℂ)*(H 2 f₀ g₁+H 2 f₁ g₀)+
    (α:ℂ)^2*(H 3 f₀ g₁+H 3 f₁ g₀)+
    H 0 f₁ g₁+(α:ℂ)*H 1 f₁ g₁+(α:ℂ)^2*H 2 f₁ g₁+
    (α:ℂ)^3*H 3 f₁ g₁+c*(α:ℂ)^4*inner ℂ (f₁:CircleL2 T) (g₁:CircleL2 T)

end Lemniscate
