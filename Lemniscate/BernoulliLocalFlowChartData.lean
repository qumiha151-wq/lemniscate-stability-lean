import Lemniscate.BernoulliArclengthFrame
import Lemniscate.PhysicalTimeInverse
import Lemniscate.ElasticFlowNormalization
import Lemniscate.NormalGraphModulation
import Lemniscate.BernoulliSobolevLinearization
import Lemniscate.NormalGraphAngularVelocity
import Lemniscate.PeriodicParabolicSpace

/-! Local identification data for a given physical free elastic flow.
The neighborhood contains actual normalized curve data, while its
phase-fixed graph and parabolic solution are constructed by the theorem. -/
noncomputable section
namespace Lemniscate
open Complex Set Filter MeasureTheory
open scoped ContDiff Topology ComplexConjugate ENNReal

abbrev bernoulliAuxiliaryCurve (e : ℝ ≃o ℝ) (x : ℝ) : ℂ :=
  (Real.sqrt 2:ℂ)*bernoulliCurve (e.symm x)
abbrev bernoulliAuxiliaryTangent (e : ℝ ≃o ℝ) (x : ℝ) : ℂ :=
  bernoulliVelocity (e.symm x)/(‖bernoulliVelocity (e.symm x)‖:ℂ)
abbrev bernoulliAuxiliaryCurvature (e : ℝ ≃o ℝ) (x : ℝ) : ℝ :=
  (3/Real.sqrt 2)*bernoulliProfileQ (e.symm x)

/-- An explicit normalized neighborhood of the given physical flow.
No selected graph coordinates, phase derivative or height equation are
included in this input. -/
structure BernoulliLocalFlowNeighborhood
    (S : ℝ) [Fact (0<S)] (e : ℝ ≃o ℝ)
    (a σ₀ α₀ : ℝ) (ρ : ℝ → ℝ) (p₀ : ℂ) (χ₀ : ℝ ≃o ℝ)
    (Y : ℝ → ℝ → ℂ) (h₀ : ℝ → ℝ) (ψ : CircleL2 S) where
  timeRadius : ℝ
  angleRadius : ℝ
  timePositive : 0<timeRadius
  anglePositive : 0<angleRadius
  gamma : (ℝ × ℝ) × ℝ → ℂ
  velocity : (ℝ × ℝ) × ℝ → ℂ
  delta : ℝ
  curvatureBound : ℝ
  speedBound : ℝ
  gammaSmooth : ContDiffOn ℝ ∞ gamma
    (insert ((0:ℝ),0) (Ioo 0 timeRadius ×ˢ Ioo (-angleRadius) angleRadius) ×ˢ (univ : Set ℝ))
  referenceSmooth : ContDiff ℝ ∞ (bernoulliAuxiliaryCurve e)
  tangentSmooth : ContDiff ℝ ∞ (bernoulliAuxiliaryTangent e)
  curvatureSmooth : ContDiff ℝ ∞ (bernoulliAuxiliaryCurvature e)
  initialSmooth : ContDiff ℝ ∞ h₀
  initialPeriodic : Function.Periodic h₀ S
  gammaDerivative : ∀ q ∈ insert ((0:ℝ),0)
    (Ioo 0 timeRadius ×ˢ Ioo (-angleRadius) angleRadius), ∀ x : ℝ,
    HasDerivAt (fun s => gamma (q,s)) (velocity (q,x)) x
  referenceDerivative : ∀ x, HasDerivAt (bernoulliAuxiliaryCurve e) (bernoulliAuxiliaryTangent e x) x
  tangentDerivative : ∀ x, HasDerivAt (bernoulliAuxiliaryTangent e)
    (I*(bernoulliAuxiliaryCurvature e x:ℂ)*bernoulliAuxiliaryTangent e x) x
  tangentUnit : ∀ x, ‖bernoulliAuxiliaryTangent e x‖=1
  speed : ∀ q ∈ insert ((0:ℝ),0)
    (Ioo 0 timeRadius ×ˢ Ioo (-angleRadius) angleRadius), ∀ x, ‖velocity (q,x)‖≤speedBound
  gammaPeriodic : ∀ q ∈ insert ((0:ℝ),0)
    (Ioo 0 timeRadius ×ˢ Ioo (-angleRadius) angleRadius), Function.Periodic (fun x => gamma (q,x)) S
  referencePeriodic : Function.Periodic (bernoulliAuxiliaryCurve e) S
  tangentPeriodic : Function.Periodic (bernoulliAuxiliaryTangent e) S
  curvaturePeriodic : Function.Periodic (bernoulliAuxiliaryCurvature e) S
  initial : ∀ x, gamma ((0,0),x)=bernoulliAuxiliaryCurve e x+
    I*((Real.sqrt 2*h₀ x:ℝ):ℂ)*bernoulliAuxiliaryTangent e x
  deltaPositive : 0<delta
  curvatureNonnegative : 0≤curvatureBound
  projectionSmall : delta+2*curvatureBound*delta<1/2
  graphRegular : curvatureBound*(delta+2*speedBound*delta)<1
  positionClose : ∀ q ∈ insert ((0:ℝ),0)
    (Ioo 0 timeRadius ×ˢ Ioo (-angleRadius) angleRadius), ∀ x,
    ‖gamma (q,x)-bernoulliAuxiliaryCurve e x‖≤delta
  tangentClose : ∀ q ∈ insert ((0:ℝ),0)
    (Ioo 0 timeRadius ×ˢ Ioo (-angleRadius) angleRadius), ∀ x,
    ‖velocity (q,x)-bernoulliAuxiliaryTangent e x‖≤delta
  curvatureBounded : ∀ x, |bernoulliAuxiliaryCurvature e x|≤curvatureBound
  coupling : ∀ q ∈ insert ((0:ℝ),0)
    (Ioo 0 timeRadius ×ˢ Ioo (-angleRadius) angleRadius), ∀ x,
    gamma (q,x)=(Real.sqrt 2:ℂ)*Complex.exp ((-(α₀+q.2):ℝ)*I)*
      (Y (physicalTime a (σ₀+q.1)) (χ₀ (x/Real.sqrt 2))-p₀)/
        (ρ (physicalTime a (σ₀+q.1)):ℂ)
  initialRotation : C(AddCircle S,ℂ)
  initialRotationValue : ∀ x : ℝ, initialRotation (x:AddCircle S)=
    (((conj (bernoulliAuxiliaryTangent e x)*bernoulliAuxiliaryCurve e x).re+
      ((conj (bernoulliAuxiliaryTangent e x)*bernoulliAuxiliaryCurve e x).im+Real.sqrt 2*h₀ x)*
        deriv (fun s => Real.sqrt 2*h₀ s) x/
          (1-bernoulliAuxiliaryCurvature e x*(Real.sqrt 2*h₀ x)):ℝ):ℂ)
  initialPair : (inner ℂ ψ (circleContinuousL2 S initialRotation)).re≠0
  originalParameterSmooth : ContDiff ℝ ∞ (χ₀ : ℝ → ℝ)
  originalParameterInverseSmooth : ContDiff ℝ ∞ (χ₀.symm : ℝ → ℝ)
  scale : ∀ t : ℝ, 0≤t → 0<ρ t ∧ ρ t=(a^4+30*t)^(1/4:ℝ) ∧
    (0<t → HasDerivAt ρ ((15/2:ℝ)*(ρ t)⁻¹^3) t ∧
      HasDerivAt (normalizedTime a) ((ρ t)⁻¹^4) t)
  flowSpace : ∀ t : ℝ, 0<t → ContDiff ℝ ∞ (Y t)
  flowRegular : ∀ t : ℝ, 0<t → ∀ s, deriv (Y t) s≠0
  flowDifferentiable : ∀ t : ℝ, 0<t → ∀ s,
    DifferentiableAt ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (t,s)
  flowEquation : ∀ t : ℝ, 0<t → ∀ s,
    (conj (deriv (fun z => Y z s) t)*(I*deriv (Y t) s/(‖deriv (Y t) s‖:ℂ))).re=
      -planarElasticForce (Y t) s

private def localComparisonProperty
    (S : ℝ) [Fact (0<S)] (q p : C(AddCircle S,ℂ))
    (ψ : CircleL2 S) (η : ℝ) (x₀ : CircleSobolevSpace S 2)
    (radius : ℝ) (high : ℝ → CircleSobolevSpace S 4) (angle : ℝ → ℝ) : Prop :=
  ∀ d>0, d≤radius → ∃ R : CircleParabolicSpace S d,
    (∀ r : unitInterval,circleParabolicCurve S d R r=
      circleSobolevInclusion S 2 (circleSobolevInclusion S 3 (high (d*(r:ℝ))))) ∧
    circleParabolicInitialValue S d R=x₀ ∧ ‖circleParabolicCurve S d R‖<η ∧
    (∀ᵐ r : unitInterval ∂volume,circleParabolicH4 S d R r=high (d*(r:ℝ))) ∧
    (∀ᵐ r ∂volume,circleParabolicTimeDerivative S d R r=
      circleNormalGraphModulatedFlow S (circleBernoulliBackground S q p) (15/2) ψ
        (circleParabolicH4 S d R r)) ∧
    ∀ r ∈ Ioo (0:ℝ) 1,((deriv angle (d*r):ℝ):ℂ)=
      circleNormalGraphAngularVelocity S (circleBernoulliBackground S q p) (15/2) ψ (high (d*r))

set_option maxHeartbeats 800000 in
/-- The actual closed height path, physical graph and exact-duration
parabolic comparison data of the given flow. -/
structure BernoulliLocalFlowChart
    (S : ℝ) [Fact (0<S)] (e : ℝ ≃o ℝ) (q p : C(AddCircle S,ℂ))
    (ψ : CircleL2 S) (η : ℝ) (x₀ : CircleSobolevSpace S 2)
    (a σ₀ α₀ : ℝ) (ρ : ℝ → ℝ) (p₀ : ℂ) (χ₀ : ℝ ≃o ℝ) (Y : ℝ → ℝ → ℂ) where
  timeRadius : ℝ
  timePositive : 0<timeRadius
  chiAux : (ℝ × ℝ) × ℝ → ℝ
  heightAux : (ℝ × ℝ) × ℝ → ℝ
  angle : ℝ → ℝ
  angleZero : angle 0=0
  angleTrace : Tendsto angle (𝓝[>] (0:ℝ)) (𝓝 0)
  angleSmooth : ContDiffOn ℝ 1 angle (Ioo 0 timeRadius)
  chiInitial : ∀ x, chiAux ((0,0),x)=x
  chiSmooth : ∀ r ∈ Ico 0 timeRadius, ContDiff ℝ ∞ (fun x => chiAux ((r,angle r),x))
  chiPositive : ∀ r ∈ Ico 0 timeRadius, ∀ x, 0<deriv (fun s => chiAux ((r,angle r),s)) x
  chiDeck : ∀ r ∈ Ico 0 timeRadius, ∀ x, chiAux ((r,angle r),x+S)=chiAux ((r,angle r),x)+S
  chiBound : ∃ R : ℝ, ∀ r ∈ Ico 0 timeRadius, ∀ x,
    |chiAux ((r,angle r),x)-x|≤R
  high : ℝ → CircleSobolevSpace S 4
  jet : ℝ → Fin 5 → C(AddCircle S,ℂ)
  highContinuous : ContinuousOn high (Ico 0 timeRadius)
  coordinates : ∀ r ∈ Ico 0 timeRadius, ∀ j,
    circleSobolevCoordinate S 4 j (high r)=circleContinuousL2 S (jet r j)
  initial : circleSobolevInclusion S 2 (circleSobolevInclusion S 3 (high 0))=x₀
  heightValue : ∀ r ∈ Ico 0 timeRadius, ∀ x : ℝ,
    jet r 0 (x:AddCircle S)=((heightAux ((r,angle r),x)/Real.sqrt 2:ℝ):ℂ)
  phase : ∀ r ∈ Ico 0 timeRadius,
    inner ℂ ψ (circleContinuousL2 S (jet r 0))=0
  physicalGraph : ∀ r ∈ Ico 0 timeRadius, ∀ s : ℝ,
    Y (physicalTime a (σ₀+r)) (χ₀ (chiAux ((r,angle r),Real.sqrt 2*s)/Real.sqrt 2))=
      p₀+(ρ (physicalTime a (σ₀+r)):ℂ)*
        (Complex.exp (((α₀+angle r):ℂ)*I)*
          (bernoulliCurve (e.symm (Real.sqrt 2*s))+
            ((jet r 0 ((Real.sqrt 2*s):AddCircle S)).re:ℂ)*
              (I*bernoulliAuxiliaryTangent e (Real.sqrt 2*s))))
  comparisonRadius : ℝ
  comparisonPositive : 0<comparisonRadius
  comparisonShort : comparisonRadius<timeRadius
  comparison : localComparisonProperty S q p ψ η x₀ comparisonRadius high angle

end Lemniscate
