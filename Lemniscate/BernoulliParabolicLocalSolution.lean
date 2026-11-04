import Lemniscate.BernoulliCoverModulationData
import Lemniscate.PeriodicParabolicLocalSolution
import Lemniscate.NormalGraphModulationConjugation
import Lemniscate.PeriodicParabolicConjugation

/-! Local solutions of the actual complex rotation-modulated Bernoulli
normal-graph equation on every positive cover. The spatial tame estimate,
equilibrium and linearization come from the actual profile. The linear
solution map is constructed by the principal solver and bounded lower-order
perturbation. This theorem does not assert realness, smoothing, or recovery
of the geometric curve flow. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Filter
open scoped ENNReal ComplexConjugate

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

private theorem bernoulli_parabolic_local_of_data
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Q P : C(AddCircle S, ℂ))
    (Ψ : CircleL2 S) (hK : K = circleBernoulliBackground S Q P)
    (hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1)
    (hFzero : circleNormalGraphModulatedFlow S K (15/2) Ψ 0 = 0)
    (hdata : ∃ δ₀ > 0, ∃ C > 0,
      (∀ f : CircleSobolevSpace S 4,
        ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖ < δ₀ →
        circleNormalGraphRotationFunctional S Ψ
          (circleNormalGraphModulatedFlow S K (15/2) Ψ f) = 0) ∧
      ∀ f g : CircleSobolevSpace S 4,
        ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖ < δ₀ →
        ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 g)‖ < δ₀ →
        ‖circleNormalGraphModulatedFlow S K (15/2) Ψ f-
            circleNormalGraphModulatedFlow S K (15/2) Ψ g-
            circleNormalGraphDerivative S K (15/2) (f-g)‖ ≤
          C*((‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖+
                ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 g)‖)*‖f-g‖+
            (‖f‖+‖g‖)*‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 (f-g))‖))
    (η : ℝ) (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ ε > 0, ∃ r > 0, r < η ∧
      ∀ u₀ : CircleSobolevSpace S 2, ‖u₀‖ ≤ ε →
        ∃! U : CircleParabolicSpace S τ,
          ‖U‖ ≤ r ∧ circleParabolicInitialValue S τ U = u₀ ∧
            ∀ᵐ t : unitInterval ∂volume,
              circleParabolicTimeDerivative S τ U t =
                circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ U t) := by
  let F := circleNormalGraphModulatedFlow S K (15/2) Ψ
  let D := circleNormalGraphDerivative S K (15/2)
  obtain ⟨δ₀,hδ₀,C,hC,_,htame⟩ := hdata
  have hD : D = circleSobolevOperator S (Q^2) ((2:ℂ) • (Q*P))
      (1-(3:ℂ) • (Q^4)) := by
    dsimp only [D]
    rw [hK]
    exact (circle_normal_graph_hasFDerivAt S (circleBernoulliBackground S Q P) (15/2)).unique
      (bernoulli_sobolev_flow_linearization S Q P hE).2
  let B : CircleSobolevSpace S 2 →L[ℂ] CircleL2 S :=
    circleSobolevCoordinate S 2 0+
      circleSobolevLowerOrderOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))
  have hBA (f : CircleSobolevSpace S 4) :
      circleSobolevPrincipalOperator S f-
        B (circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)) = -(D f) := by
    rw [hD,circle_sobolev_operator_lower_order]
    have hvalue : circleSobolevCoordinate S 2 0
        (circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)) =
      circleSobolevCoordinate S 4 0 f := rfl
    simp only [circleSobolevPrincipalOperator,B,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,hvalue]
    module
  exact circle_parabolic_local_solution S F D B hFzero hBA δ₀ hδ₀ C hC.le htame η hη

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

set_option maxHeartbeats 800000 in
/-- Small H2 initial heights admit a local solution of the actual complex
modulated equation, unique in a parabolic-norm ball smaller than any
prescribed positive radius, with the given normalized adjoint vector. -/
private theorem bernoulli_cover_modulated_local_solution
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) (η : ℝ) (hη : 0 < η) :
    let E := circlePeriodicExtension T S M hS
    let Q := E q
    let P := E p
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    let K := circleBernoulliBackground S Q P
    circleConjugate S (Ψ:CircleL2 S) = (Ψ:CircleL2 S) ∧
      inner ℂ (Ψ:CircleL2 S) (circleContinuousL2 S K.b) ≠ 0 ∧
      ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ ε > 0, ∃ r > 0, r < η ∧
          ∀ u₀ : CircleSobolevSpace S 2, ‖u₀‖ ≤ ε →
            ∃! U : CircleParabolicSpace S τ,
              ‖U‖ ≤ r ∧ circleParabolicInitialValue S τ U = u₀ ∧
                ∀ᵐ t : unitInterval ∂volume,
                  circleParabolicTimeDerivative S τ U t =
                    circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S)
                      (circleParabolicH4 S τ U t) := by
  dsimp only
  let E := circlePeriodicExtension T S M hS
  let Q := E q
  let P := E p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let K := circleBernoulliBackground S Q P
  have hdata := (paper_periodic_cover_modulated_tame_data T S q p hq hp he
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS).2.2
  have hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1 :=
    fun x => he (circleCoverProjection T S M hS x)
  exact ⟨hdata.1,hdata.2.1,
    bernoulli_parabolic_local_of_data S K Q P (Ψ:CircleL2 S) rfl hE
      hdata.2.2.2.1 hdata.2.2.2.2.2 η hη⟩

end Profile
end Lemniscate

end

/-! Realness of the actual local modulated solution follows from conjugation
and uniqueness in the same parabolic ball. A given actual normalized
adjoint vector is used throughout, and the ball can be chosen smaller
than any prescribed positive radius. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Filter
open scoped ENNReal ComplexConjugate

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

private theorem real_local_witness_transport
    {H : Type*} {X : ℝ → Type*} (N : H → ℝ)
    (P : ∀ τ : ℝ, ℝ → H → X τ → Prop) (R : H → Prop)
    (J : ∀ τ : ℝ, X τ → X τ)
    (hJ : ∀ τ r u₀, R u₀ → ∀ U, P τ r u₀ U → P τ r u₀ (J τ U))
    (η : ℝ)
    (h : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ ε > 0, ∃ r > 0, r < η ∧
      ∀ u₀, N u₀ ≤ ε → ∃! U, P τ r u₀ U) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ ε > 0, ∃ r > 0, r < η ∧
      ∀ u₀, N u₀ ≤ ε → ∃ U, P τ r u₀ U ∧
        (R u₀ → J τ U = U) ∧ ∀ V, P τ r u₀ V → V = U := by
  obtain ⟨τ,hτ,hτ1,ε,hε,r,hr,hrη,hsolve⟩ := h
  refine ⟨τ,hτ,hτ1,ε,hε,r,hr,hrη,?_⟩
  intro u₀ hu₀
  obtain ⟨U,hU,hunique⟩ := hsolve u₀ hu₀
  exact ⟨U,hU,(fun hR => hunique (J τ U) (hJ τ r u₀ hR U hU)),hunique⟩

private theorem parabolic_real_local_of_data
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Ψ : CircleL2 S)
    (hKstar : (⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩ :
      BackgroundJetOver C(AddCircle S, ℂ)) = K)
    (hΨreal : circleConjugate S Ψ = Ψ) (η : ℝ)
    (hlocal : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ ε > 0, ∃ r > 0, r < η ∧
      ∀ u₀ : CircleSobolevSpace S 2, ‖u₀‖ ≤ ε →
        ∃! U : CircleParabolicSpace S τ,
          ‖U‖ ≤ r ∧ circleParabolicInitialValue S τ U = u₀ ∧
            ∀ᵐ t : unitInterval ∂volume,
              circleParabolicTimeDerivative S τ U t =
                circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ U t)) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ ε > 0, ∃ r > 0, r < η ∧
          ∀ u₀ : CircleSobolevSpace S 2, ‖u₀‖ ≤ ε →
            ∃ U : CircleParabolicSpace S τ,
              (‖U‖ ≤ r ∧ circleParabolicInitialValue S τ U = u₀ ∧
                (∀ᵐ t : unitInterval ∂volume,
                  circleParabolicTimeDerivative S τ U t =
                    circleNormalGraphModulatedFlow S K (15/2) Ψ
                      (circleParabolicH4 S τ U t))) ∧
                (circleSobolevConjugation S 2 u₀ = u₀ →
                  circleParabolicConjugation S τ U = U) ∧
                ∀ V : CircleParabolicSpace S τ,
                  (‖V‖ ≤ r ∧ circleParabolicInitialValue S τ V = u₀ ∧
                    ∀ᵐ t : unitInterval ∂volume,
                      circleParabolicTimeDerivative S τ V t =
                        circleNormalGraphModulatedFlow S K (15/2) Ψ
                          (circleParabolicH4 S τ V t)) → V = U := by
  let F := circleNormalGraphModulatedFlow S K (15/2) Ψ
  have hFstar (f : CircleSobolevSpace S 4) :
      circleConjugate S (F f) = F (circleSobolevConjugation S 4 f) := by
    have h := circle_normal_graph_modulated_flow_conjugation S K (15/2) (Ψ:CircleL2 S) f
    rw [hKstar,hΨreal] at h
    exact h
  refine real_local_witness_transport
    (H := CircleSobolevSpace S 2) (X := fun τ => CircleParabolicSpace S τ)
    (fun u => ‖u‖)
    (fun τ r u₀ U => ‖U‖ ≤ r ∧ circleParabolicInitialValue S τ U = u₀ ∧
      ∀ᵐ t : unitInterval ∂volume,
        circleParabolicTimeDerivative S τ U t = F (circleParabolicH4 S τ U t))
    (fun u₀ => circleSobolevConjugation S 2 u₀ = u₀)
    (fun τ U => circleParabolicConjugation S τ U) ?_ η hlocal
  intro τ r u₀ h₀real U hU
  have hcomponents := circle_parabolic_conjugation_components S τ U
  have hH := hcomponents.2.1
  have hV := hcomponents.2.2.1
  have hI := hcomponents.2.2.2
  have hnormU : ‖circleParabolicConjugation S τ U‖ ≤ r := by
    have hn := (circleParabolicConjugation S τ).norm_map U
    simpa only using! hn.trans_le hU.1
  have hinitial : circleParabolicInitialValue S τ (circleParabolicConjugation S τ U) = u₀ := by
    exact hI.trans ((congrArg (circleSobolevConjugation S 2) hU.2.1).trans h₀real)
  have hPDE : ∀ᵐ t : unitInterval ∂volume,
      circleParabolicTimeDerivative S τ (circleParabolicConjugation S τ U) t =
        F (circleParabolicH4 S τ (circleParabolicConjugation S τ U) t) := by
    filter_upwards [hH,hV,hU.2.2] with t hHt hVt hUt
    calc
      circleParabolicTimeDerivative S τ (circleParabolicConjugation S τ U) t =
          circleConjugate S (circleParabolicTimeDerivative S τ U t) := hVt
      _ = circleConjugate S (F (circleParabolicH4 S τ U t)) := congrArg (circleConjugate S) hUt
      _ = F (circleSobolevConjugation S 4 (circleParabolicH4 S τ U t)) := hFstar _
      _ = F (circleParabolicH4 S τ (circleParabolicConjugation S τ U) t) :=
        congrArg F hHt.symm
  exact ⟨hnormU,hinitial,hPDE⟩


section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

/-- The actual complex local solution stays fixed by conjugation whenever
its initial height is real. Existence and uniqueness hold on the same ball
for all sufficiently small complex initial heights. -/
theorem bernoulli_cover_modulated_real_local_solution
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) (η : ℝ) (hη : 0 < η) :
    let E := circlePeriodicExtension T S M hS
    let Q := E q
    let P := E p
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    let K := circleBernoulliBackground S Q P
    circleConjugate S (Ψ:CircleL2 S) = (Ψ:CircleL2 S) ∧
      inner ℂ (Ψ:CircleL2 S) (circleContinuousL2 S K.b) ≠ 0 ∧
      ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ ε > 0, ∃ r > 0, r < η ∧
          ∀ u₀ : CircleSobolevSpace S 2, ‖u₀‖ ≤ ε →
            ∃ U : CircleParabolicSpace S τ,
              (‖U‖ ≤ r ∧ circleParabolicInitialValue S τ U = u₀ ∧
                (∀ᵐ t : unitInterval ∂volume,
                  circleParabolicTimeDerivative S τ U t =
                    circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S)
                      (circleParabolicH4 S τ U t))) ∧
                (circleSobolevConjugation S 2 u₀ = u₀ →
                  circleParabolicConjugation S τ U = U) ∧
                ∀ V : CircleParabolicSpace S τ,
                  (‖V‖ ≤ r ∧ circleParabolicInitialValue S τ V = u₀ ∧
                    ∀ᵐ t : unitInterval ∂volume,
                      circleParabolicTimeDerivative S τ V t =
                        circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S)
                          (circleParabolicH4 S τ V t)) → V = U := by
  dsimp only
  let E := circlePeriodicExtension T S M hS
  let Q := E q
  let P := E p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let K := circleBernoulliBackground S Q P
  have hlocal :=
    bernoulli_cover_modulated_local_solution T S q p hq hp he hqreal hpreal hs hc ho hr
      ψ hnorm hψzero M hM hS η hη
  have hQreal : ∀ x, conj (Q x) = Q x :=
    circle_periodic_extension_real T S M hS q hqreal
  have hPreal : ∀ x, conj (P x) = P x :=
    circle_periodic_extension_real T S M hS p hpreal
  have hQstar : star Q = Q := by
    apply ContinuousMap.ext
    intro x
    exact hQreal x
  have hPstar : star P = P := by
    apply ContinuousMap.ext
    intro x
    exact hPreal x
  have hmul (a b : C(AddCircle S, ℂ)) : star (a*b) = star a*star b :=
    (starRingEnd C(AddCircle S, ℂ)).map_mul a b
  have hKstar : (⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩ :
      BackgroundJetOver C(AddCircle S, ℂ)) = K := by
    simp [K,circleBernoulliBackground,star_smul,hmul,hQstar,hPstar,Complex.star_def]
  exact ⟨hlocal.1,hlocal.2.1,
    parabolic_real_local_of_data S K (Ψ:CircleL2 S) hKstar hlocal.1 η hlocal.2.2⟩

end Profile
end Lemniscate
