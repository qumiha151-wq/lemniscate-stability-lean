import Lemniscate.BernoulliCoverModulationData
import Lemniscate.BernoulliSobolevLinearization
import Lemniscate.NormalGraphLowSobolevCoordinates
import Lemniscate.PeriodicParabolicNonlinearUniqueness
import Lemniscate.TameNonlinearContinuity

/-! One H2 neighborhood supplies the domain, phase normalization,
continuity and finite-interval uniqueness of the actual covered equation. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set CoarseArithmetic
open scoped Topology ENNReal ComplexConjugate

private abbrev LocalProfileNeighborhood
    (T : ℝ) [Fact (0<T)] (K : BackgroundJetOver C(AddCircle T,ℂ))
    (ψ : CircleL2 T) (η : ℝ) : Prop :=
  (∀ f : CircleSobolevSpace T 4,
    ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖<η →
      f∈circleNormalGraphDomain T K) ∧
  (∀ h : CircleSobolevSpace T 2,‖h‖<η →
    circleNormalGraphRotationFunctional T ψ (circleNormalGraphRotationField T K h)≠0) ∧
  ContinuousOn (circleNormalGraphModulatedFlow T K (15/2) ψ)
    {f : CircleSobolevSpace T 4 |
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖<η} ∧
  ∀ d : ℝ,0<d → ∀ U V : CircleParabolicSpace T d,
    circleParabolicInitialValue T d U=circleParabolicInitialValue T d V →
    ‖circleParabolicCurve T d U‖<η → ‖circleParabolicCurve T d V‖<η →
    (∀ᵐ r : unitInterval ∂volume,circleParabolicTimeDerivative T d U r=
      circleNormalGraphModulatedFlow T K (15/2) ψ (circleParabolicH4 T d U r)) →
    (∀ᵐ r : unitInterval ∂volume,circleParabolicTimeDerivative T d V r=
      circleNormalGraphModulatedFlow T K (15/2) ψ (circleParabolicH4 T d V r)) → U=V

private theorem local_profile_radius_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ a>0,P a) (k : ∀ a,0<a → P a → Q) : Q := by
  obtain ⟨a,ha,hP⟩ := h
  exact k a ha hP

private theorem local_profile_two_radius_transport {P : ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ a>0,∃ b>0,P a b) (k : ∀ a,0<a → ∀ b,0<b → P a b → Q) : Q := by
  obtain ⟨a,ha,b,hb,hP⟩ := h
  exact k a ha b hb hP

set_option maxHeartbeats 800000 in
private theorem local_profile_neighborhood_of_tame
    (T : ℝ) [Fact (0<T)] (K : BackgroundJetOver C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (hpair : inner ℂ ψ (circleContinuousL2 T K.b)≠0)
    (D : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T)
    (hBA : ∀ f,circleSobolevPrincipalOperator T f-
      B (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))= -(D f))
    (δ₀ C : ℝ) (hδ₀ : 0<δ₀) (hC : 0≤C)
    (htame : ∀ f g : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖<δ₀ →
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖<δ₀ →
      ‖circleNormalGraphModulatedFlow T K (15/2) ψ f-
        circleNormalGraphModulatedFlow T K (15/2) ψ g-D (f-g)‖≤
        C*((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
          ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
            (‖f‖+‖g‖)*‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖)) :
    ∃ η>0,LocalProfileNeighborhood T K ψ η := by
  have hnormal := (circle_normal_graph_rotation_normalization T K ψ hpair).2.2.2.2
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnormal
  refine local_profile_radius_transport
    (circle_parabolic_nonlinear_uniqueness T
      (circleNormalGraphModulatedFlow T K (15/2) ψ) D B hBA δ₀ C hδ₀ hC htame) ?_
  intro δ hδ huniqueness
  obtain ⟨hδ₀le,hunique⟩ := huniqueness
  let η := min r δ
  have hηr : η≤r := min_le_left _ _
  have hηδ : η≤δ := min_le_right _ _
  have hηδ₀ : η≤δ₀ := hηδ.trans hδ₀le
  have hsmall (h : CircleSobolevSpace T 2) (hh : ‖h‖<η) :
      circleNormalGraphLowCoordinates T h∈normalGraphLowerCoefficientDomain T K ∧
        circleNormalGraphRotationFunctional T ψ (circleNormalGraphRotationField T K h)≠0 := by
    have hp := hball (show h∈Metric.ball (0:CircleSobolevSpace T 2) r by
      simpa only [Metric.mem_ball,dist_zero_right] using hh.trans_le hηr)
    exact ⟨hp.1,hp.2.1⟩
  refine ⟨η,lt_min hr hδ,?_,?_,?_,?_⟩
  · intro f hf
    exact (circle_normal_graph_domain_iff_low T K f).mpr (hsmall _ hf).1
  · intro h hh
    exact (hsmall h hh).2
  · let S₂ : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
      (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
    exact tame_nonlinear_continuousOn D S₂
      {f : CircleSobolevSpace T 4 | ‖S₂ f‖<η} C
      (circleNormalGraphModulatedFlow T K (15/2) ψ)
      (fun f hf g hg => htame f g (hf.trans_le hηδ₀) (hg.trans_le hηδ₀))
  · intro d hd U V hinit hU hV hPU hPV
    exact hunique d hd U V hinit (hU.trans_le hηδ) (hV.trans_le hηδ) hPU hPV

variable (T S : ℝ) [Fact (0<T)] [Fact (0<S)]

set_option maxHeartbeats 800000 in
/-- Actual covered Bernoulli profile data give one low-H2 neighborhood
for the rational domain, nonzero phase denominator, continuity of the
modulated H4-to-L2 flow, and uniqueness on every positive time interval.
No smallness of the H4 norm or the maximal-regularity norm is required. -/
theorem bernoulli_cover_local_profile_neighborhood
    (q p : C(AddCircle T,ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (hE : ∀ x,2*(p x)^2+(q x)^4=1)
    (hqreal : ∀ x,conj (q x)=q x) (hpreal : ∀ x,conj (p x)=p x)
    (hs : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (-n)=
      fourierCoeff (q^2:C(AddCircle T,ℂ)) n)
    (hc : ∀ j : ℕ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (2*(j:ℤ))=
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (2*n+1)=0)
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p)=1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ=0)
    (M : ℕ) (hM : 0<M) (hS : S=(M:ℝ)*T) :
    let Q := circlePeriodicExtension T S M hS q
    let P := circlePeriodicExtension T S M hS p
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    ∃ η>0,LocalProfileNeighborhood S (circleBernoulliBackground S Q P) (Ψ:CircleL2 S) η := by
  dsimp only
  let Q := circlePeriodicExtension T S M hS q
  let P := circlePeriodicExtension T S M hS p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let K := circleBernoulliBackground S Q P
  let D := circleNormalGraphDerivative S K (15/2)
  let B := circleSobolevCoordinate S 2 0+
    circleSobolevLowerOrderOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • Q^4)
  have hE' : ∀ x,2*(P x)^2+(Q x)^4=1 :=
    fun x => hE (circleCoverProjection T S M hS x)
  have hD : D=circleSobolevOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • Q^4) :=
    (circle_normal_graph_hasFDerivAt S K (15/2)).unique
      (bernoulli_sobolev_flow_linearization S Q P hE').2
  have hBA (f : CircleSobolevSpace S 4) : circleSobolevPrincipalOperator S f-
      B (circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f))= -(D f) := by
    rw [hD,circle_sobolev_operator_lower_order]
    have hv : circleSobolevCoordinate S 2 0
        (circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f))=
          circleSobolevCoordinate S 4 0 f := rfl
    simp only [B,circleSobolevPrincipalOperator,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,hv]
    module
  have hdata := (paper_periodic_cover_modulated_tame_data T S q p hq hp hE hqreal hpreal
    hs hc ho hr ψ hnorm hψzero M hM hS).2.2
  refine local_profile_two_radius_transport hdata.2.2.2.2.2 ?_
  intro δ₀ hδ₀ C hC htame
  exact local_profile_neighborhood_of_tame S K (Ψ:CircleL2 S) hdata.2.1 D B hBA
    δ₀ C hδ₀ hC.le htame.2

end Lemniscate
