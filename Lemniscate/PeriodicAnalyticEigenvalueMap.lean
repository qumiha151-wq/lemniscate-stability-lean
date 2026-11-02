import Lemniscate.PeriodicPrincipalBlochCoefficients
import Mathlib.Analysis.Analytic.Constructions

/-! A complex analytic normalized eigenvalue equation on C x (C x L2).
At real parameters it is exactly the original H4-domain eigenvalue equation
expressed using the principal inverse. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]
attribute [local fun_prop] analyticAt_fst analyticAt_snd

theorem circle_principal_bloch_family_analytic (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (z : ℂ) :
    AnalyticAt ℂ (circlePrincipalBlochFamily T h h₁ h₂ p hp) z := by
  unfold circlePrincipalBlochFamily
  fun_prop

noncomputable def circleNormalizedEigenvalueMap (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (ψ : CircleL2 T) (v : ℂ × (ℂ × CircleL2 T)) :
    ℂ × (CircleL2 T × ℂ) :=
  (v.1,(circlePrincipalBlochFamily T h h₁ h₂ p hp v.1 v.2.2-
    v.2.1 • circlePrincipalResolvent T (p^4) (by positivity) v.2.2,
    ((innerSL ℂ ψ).comp (circlePrincipalResolvent T (p^4) (by positivity))) v.2.2))

theorem circle_normalized_eigenvalue_map_analytic (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (ψ : CircleL2 T) (v : ℂ × (ℂ × CircleL2 T)) :
    AnalyticAt ℂ (circleNormalizedEigenvalueMap T h h₁ h₂ p hp ψ) v := by
  unfold circleNormalizedEigenvalueMap circlePrincipalBlochFamily
  simp only [add_apply,smul_apply]
  have hz : AnalyticAt ℂ (fun w : ℂ × (ℂ × CircleL2 T) => w.1) v := analyticAt_fst
  have ha : AnalyticAt ℂ (fun w : ℂ × (ℂ × CircleL2 T) => w.2.1) v :=
    analyticAt_fst.comp analyticAt_snd
  have hx : AnalyticAt ℂ (fun w : ℂ × (ℂ × CircleL2 T) => w.2.2) v :=
    analyticAt_snd.comp analyticAt_snd
  have hc (j : Fin 5) : AnalyticAt ℂ (fun w : ℂ × (ℂ × CircleL2 T) =>
      circlePrincipalBlochCoefficient T h h₁ h₂ p hp j w.2.2) v :=
    (circlePrincipalBlochCoefficient T h h₁ h₂ p hp j).analyticAt _ |>.comp hx
  have hr : AnalyticAt ℂ (fun w : ℂ × (ℂ × CircleL2 T) =>
      circlePrincipalResolvent T (p^4) (by positivity) w.2.2) v :=
    (circlePrincipalResolvent T (p^4) (by positivity)).analyticAt _ |>.comp hx
  have hn : AnalyticAt ℂ (fun w : ℂ × (ℂ × CircleL2 T) =>
      ((innerSL ℂ ψ).comp (circlePrincipalResolvent T (p^4) (by positivity))) w.2.2) v :=
    (((innerSL ℂ ψ).comp (circlePrincipalResolvent T (p^4)
      (by positivity))).analyticAt _).comp hx
  exact hz.prod ((((((hc 0).add (hz.smul (hc 1))).add ((hz.pow 2).smul (hc 2))).add
    ((hz.pow 3).smul (hc 3))).add ((hz.pow 4).smul (hc 4))).sub (ha.smul hr) |>.prod hn)

theorem circle_normalized_eigenvalue_map_real (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (ψ : CircleL2 T) (α : ℝ) (a : ℂ) (f : CircleL2 T) :
    circleNormalizedEigenvalueMap T h h₁ h₂ p hp ψ ((α:ℂ),(a,f)) =
      ((α:ℂ),(circleBlochOperator T h h₁ h₂ α (circlePrincipalResolventH4 T (p^4) (by positivity) f)-
        a • circlePrincipalResolvent T (p^4) (by positivity) f,
        inner ℂ ψ (circlePrincipalResolvent T (p^4) (by positivity) f))) := by
  rw [circleNormalizedEigenvalueMap,circle_principal_bloch_family_real]
  rfl

end Lemniscate
