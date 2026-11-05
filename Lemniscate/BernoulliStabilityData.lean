import Lemniscate.BernoulliCircleProfile
import Lemniscate.BernoulliProfileIdentification
import Lemniscate.BernoulliReferenceLength
import Lemniscate.PeriodicAdjointNeutral

/-! All profile, Fourier and normalized adjoint data used by the geometric
main theorem are constructed from the explicit Bernoulli lemniscate.
There are no assumed profile or spectral identities in the existence result. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

/-- The actual one-cover data, chosen once before all covering numbers. -/
structure BernoulliStabilityData (T : ℝ) [Fact (0<T)] where
  coordinate : ℝ ≃o ℝ
  arclength : ∀ u,coordinate u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖
  period : T=coordinate (2*Real.pi)
  length : T=4*Khalf
  q : C(AddCircle T,ℂ)
  p : C(AddCircle T,ℂ)
  qDerivative : HasCircleDeriv T q p
  pDerivative : HasCircleDeriv T p (-(q^3))
  energy : ∀ x,2*(p x)^2+(q x)^4=1
  qReal : ∀ x,conj (q x)=q x
  pReal : ∀ x,conj (p x)=p x
  curvature : ∀ x : ℝ,(planarSignedCurvature bernoulliCurve (coordinate.symm x):ℂ)=
    3*q (x:AddCircle T)
  qValue : ∀ x : ℝ,q (x:AddCircle T)=(bernoulliProfileQ (coordinate.symm x):ℂ)
  pValue : ∀ x : ℝ,p (x:AddCircle T)=(bernoulliProfileP (coordinate.symm x):ℂ)
  fourierSymmetry : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (-n)=
    fourierCoeff (q^2:C(AddCircle T,ℂ)) n
  evenFourier : ∀ j : ℕ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (2*(j:ℤ))=
    (fourierCoefficient lemniscateFrequencySquared nome j:ℂ)
  oddFourier : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (2*n+1)=0
  frequency : (2*Real.pi/T)^2=lemniscateFrequencySquared
  adjoint : circleH4Domain T
  adjointNormalization : inner ℂ (adjoint:CircleL2 T) (circleUnitRotation T q p)=1
  adjointEquation : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) adjoint=0

/-- The geometric stability data exist for the actual Bernoulli curve,
including its exact elliptic-integral length and its actual adjoint vector. -/
theorem bernoulli_stability_data_exists :
    ∃ T : ℝ,∃ hT : 0<T,
      letI : Fact (0<T) := ⟨hT⟩
      Nonempty (BernoulliStabilityData T) := by
  obtain ⟨e,he,hT,hdata⟩ := bernoulli_circle_profile_exists
  let T := e (2*Real.pi)
  letI : Fact (0<T) := ⟨hT⟩
  obtain ⟨q,p,hq,hp,hE,hqreal,hpreal,_,_,hcurv,hs,hc,ho,_,_,
    c,hcpos,hnorm,hperiod,hr,hW,hW₁⟩ := hdata
  obtain ⟨ψ,hψ,_⟩ := paper_single_period_adjoint_vector T q p hq hp hE
    hqreal hpreal hs hc ho hr
  have hlength : T=4*Khalf := by
    have hsqrt : Real.sqrt (2:ℝ)≠0 :=
      (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
    calc
      T=Real.sqrt 2*(∫ t in (0:ℝ)..(2*Real.pi),‖bernoulliVelocity t‖) := by
        rw [show T=e (2*Real.pi) from rfl,he,intervalIntegral.integral_const_mul]
      _=Real.sqrt 2*(4*Khalf/Real.sqrt 2) := by rw [bernoulli_reference_length]
      _=4*Khalf := by field_simp [hsqrt]
  refine ⟨T,hT,⟨?_⟩⟩
  exact {
    coordinate := e
    arclength := he
    period := rfl
    length := hlength
    q := q
    p := p
    qDerivative := hq
    pDerivative := hp
    energy := hE
    qReal := hqreal
    pReal := hpreal
    curvature := hcurv
    qValue := fun x => (bernoulli_circle_profile_identification e he q p hq hcurv x).1
    pValue := fun x => (bernoulli_circle_profile_identification e he q p hq hcurv x).2
    fourierSymmetry := hs
    evenFourier := hc
    oddFourier := ho
    frequency := hr
    adjoint := ψ
    adjointNormalization := hψ.1
    adjointEquation := hψ.2 }

end Lemniscate
