import Lemniscate.PeriodicAnalyticEigenvalueMap
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Derivative of the normalized eigenvalue equation at the neutral mode.
The parameter direction is a single off-diagonal block. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

theorem circle_principal_bloch_family_hasDerivAt_zero (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) :
    HasDerivAt (circlePrincipalBlochFamily T h h₁ h₂ p hp)
      (circlePrincipalBlochCoefficient T h h₁ h₂ p hp 1) 0 := by
  let C := circlePrincipalBlochCoefficient T h h₁ h₂ p hp
  have hid := hasDerivAt_id (0:ℂ)
  have h0 := hasDerivAt_const (0:ℂ) (C 0)
  have h1 := hid.smul_const (C 1)
  have h2 : HasDerivAt (fun z : ℂ => z^2 • C 2) 0 0 := by
    simpa using (hid.pow 2).smul_const (C 2)
  have h3 : HasDerivAt (fun z : ℂ => z^3 • C 3) 0 0 := by
    simpa using (hid.pow 3).smul_const (C 3)
  have h4 : HasDerivAt (fun z : ℂ => z^4 • C 4) 0 0 := by
    simpa using (hid.pow 4).smul_const (C 4)
  change HasDerivAt (fun z : ℂ => C 0+z • C 1+z^2 • C 2+z^3 • C 3+z^4 • C 4) (C 1) 0
  convert! ((((h0.add h1).add h2).add h3).add h4) using 1 <;>
    simp only [zero_add,add_zero,one_smul]

theorem circle_normalized_eigenvalue_map_hasFDerivAt (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (ψ x : CircleL2 T) :
    HasFDerivAt (circleNormalizedEigenvalueMap T h h₁ h₂ p hp ψ)
      ((ContinuousLinearMap.fst ℂ ℂ (ℂ × CircleL2 T)).prod
        ((((circlePrincipalBlochCoefficient T h h₁ h₂ p hp 0).comp
            ((ContinuousLinearMap.snd ℂ ℂ (CircleL2 T)).comp
              (ContinuousLinearMap.snd ℂ ℂ (ℂ × CircleL2 T)))+
          (ContinuousLinearMap.fst ℂ ℂ (ℂ × CircleL2 T)).smulRight
            (circlePrincipalBlochCoefficient T h h₁ h₂ p hp 1 x))-
          ((ContinuousLinearMap.fst ℂ ℂ (CircleL2 T)).comp
            (ContinuousLinearMap.snd ℂ ℂ (ℂ × CircleL2 T))).smulRight
              (circlePrincipalResolvent T (p^4) (by positivity) x)).prod
        (((innerSL ℂ ψ).comp (circlePrincipalResolvent T (p^4) (by positivity))).comp
          ((ContinuousLinearMap.snd ℂ ℂ (CircleL2 T)).comp
            (ContinuousLinearMap.snd ℂ ℂ (ℂ × CircleL2 T)))))) (0,(0,x)) := by
  let v : ℂ × (ℂ × CircleL2 T) := (0,(0,x))
  let Z := ContinuousLinearMap.fst ℂ ℂ (ℂ × CircleL2 T)
  let A := (ContinuousLinearMap.fst ℂ ℂ (CircleL2 T)).comp
    (ContinuousLinearMap.snd ℂ ℂ (ℂ × CircleL2 T))
  let X := (ContinuousLinearMap.snd ℂ ℂ (CircleL2 T)).comp
    (ContinuousLinearMap.snd ℂ ℂ (ℂ × CircleL2 T))
  let R := circlePrincipalResolvent T (p^4) (by positivity)
  have hZ := Z.hasFDerivAt (x := v)
  have hA := A.hasFDerivAt (x := v)
  have hX := X.hasFDerivAt (x := v)
  have hF := (circle_principal_bloch_family_hasDerivAt_zero T h h₁ h₂ p hp).hasFDerivAt.comp v hZ
  have hRX := R.hasFDerivAt.comp v hX
  have hN := ((innerSL ℂ ψ).comp R).hasFDerivAt.comp v hX
  have hd := hZ.prodMk (((hF.clm_apply hX).sub (hA.smul hRX)).prodMk hN)
  change HasFDerivAt (circleNormalizedEigenvalueMap T h h₁ h₂ p hp ψ) _ (0,(0,x)) at hd
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  simp [v,Z,A,X,R,circlePrincipalBlochFamily,ContinuousLinearMap.flip_apply]

end Lemniscate
