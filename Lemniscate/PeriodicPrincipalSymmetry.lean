import Lemniscate.PeriodicPrincipalBlochCoefficients

/-! Reflection commutes with the fourth-order principal resolvent,
including its map into the actual H4 domain. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_principal_symbol_neg (r : ℝ) (n : ℤ) :
    circlePrincipalSymbol T r (-n) = circlePrincipalSymbol T r n := by
  have hn : (-(n:ℝ))^4 = (n:ℝ)^4 := by ring
  simp only [circlePrincipalSymbol,Int.cast_neg,hn]

theorem circle_principal_resolvent_reflect (r : ℝ) (hr : 0 < r) (f : CircleL2 T) :
    circlePrincipalResolvent T r hr (circleReflect T f) =
      circleReflect T (circlePrincipalResolvent T r hr f) := by
  apply circle_fourier_ext T
  intro n
  rw [circle_principal_resolvent_fourier,circle_reflect_fourier,
    circle_reflect_fourier,circle_principal_resolvent_fourier,circle_principal_symbol_neg]

theorem circle_principal_resolvent_h4_reflect (r : ℝ) (hr : 0 < r) (f : CircleL2 T) :
    circlePrincipalResolventH4 T r hr (circleReflect T f) =
      circleReflectH4 T (circlePrincipalResolventH4 T r hr f) := by
  apply Subtype.ext
  exact circle_principal_resolvent_reflect T r hr f

theorem circle_principal_shift_reflect (r : ℝ) (f : circleH4Domain T) :
    circlePrincipalShift T r (circleReflectH4 T f) =
      circleReflect T (circlePrincipalShift T r f) := by
  change (r:ℂ) • (circleReflectH4 T f:CircleL2 T)+
    (4:ℂ) • (circleH4Jet T (circleReflectH4 T f)).fourth =
      circleReflect T ((r:ℂ) • (f:CircleL2 T)+(4:ℂ) • (circleH4Jet T f).fourth)
  rw [circle_reflect_h4_fourth,circle_reflect_add,circle_reflect_smul,circle_reflect_smul]
  rfl

end Lemniscate
