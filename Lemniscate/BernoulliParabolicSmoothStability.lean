import Lemniscate.BernoulliParabolicGlobalSolution
import Lemniscate.BernoulliParabolicGlobalSmoothing
import Lemniscate.PeriodicParabolicGlobalUniqueness
import Lemniscate.PeriodicSobolevEnergyNorm

/-! Smooth stability of the actual covered modulated Bernoulli equation.
One fixed energy estimate controls the H4 norm of every segment. Global
uniqueness identifies the auxiliary solutions used for different decay
rates with the same given global solution.
 -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set CoarseArithmetic
open scoped ENNReal Topology NNReal ComplexConjugate

private theorem smooth_stability_scalar_h4_bound
    (α C a b : ℝ) (hα : 0 < α) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : α*a^2 ≤ C*b^2) :
    a ≤ Real.sqrt (C/α)*b := by
  have hsq : a^2 ≤ (Real.sqrt (C/α)*b)^2 := by
    rw [mul_pow,Real.sq_sqrt (div_nonneg hC hα.le)]
    have hh : a^2 ≤ (C*b^2)/α := (le_div_iff₀ hα).mpr (by
      simpa only [mul_comm] using h)
    exact hh.trans_eq (by ring)
  exact (sq_le_sq₀ ha (mul_nonneg (Real.sqrt_nonneg _) hb)).mp hsq

private theorem smooth_stability_unit_time_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : Lp E 2 (volume : Measure unitInterval)) :
    (∫ t in Iic (1:unitInterval), ‖f t‖^2 ∂volume) = ‖f‖^2 := by
  have hIic : Iic (1:unitInterval) = univ := by
    ext t
    simp only [mem_Iic,mem_univ,iff_true]
    exact t.property.2
  rw [hIic,setIntegral_univ]
  exact (unit_time_l2_norm_sq f).symm

section Data
variable (S : ℝ) [Fact (0 < S)]

private theorem smooth_stability_curve_bound
    (τ : ℝ) (U : CircleParabolicSpace S τ) :
    ‖circleParabolicCurve S τ U‖ ≤ ‖U‖ := by
  change ‖U.val.1‖ ≤ ‖U.val‖
  exact norm_fst_le U.val

private theorem smooth_stability_h4_from_energy
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Ψ : CircleL2 S)
    (V : CircleL2 S →L[ℂ] CircleL2 S) (κ δ c τ : ℝ)
    (hκ : 0 < κ) (hc : 0 < c) (hτ : 0 < τ)
    (henergy : ∀ U : CircleParabolicSpace S τ,
      inner ℂ Ψ (circleSobolevCoordinate S 2 0 (circleParabolicInitialValue S τ U)) = 0 →
      ‖circleParabolicCurve S τ U‖ < δ →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ U t =
        circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ U t)) →
      (2*τ*c)*(∫ t in Iic (1:unitInterval), ‖circleParabolicH4 S τ U t‖^2 ∂volume) ≤
        ‖circleSobolevCoordinate S 2 0 (circleParabolicInitialValue S τ U)‖^2+
          4*‖circleSobolevCoordinate S 2 2 (circleParabolicInitialValue S τ U)‖^2+
          κ*‖V (circleSobolevCoordinate S 2 0 (circleParabolicInitialValue S τ U))‖^2) :
    ∃ A > 0, ∀ U : CircleParabolicSpace S τ,
      inner ℂ Ψ (circleSobolevCoordinate S 2 0 (circleParabolicInitialValue S τ U)) = 0 →
      ‖circleParabolicCurve S τ U‖ < δ →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ U t =
        circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ U t)) →
      ‖circleParabolicH4 S τ U‖ ≤ A*‖circleParabolicInitialValue S τ U‖ := by
  let C : ℝ := 4+κ*‖V‖^2
  let A : ℝ := Real.sqrt (C/(2*τ*c))
  have hC : 0 < C := by dsimp only [C]; positivity
  have hα : 0 < 2*τ*c := by positivity
  refine ⟨A,Real.sqrt_pos.mpr (div_pos hC hα),?_⟩
  intro U hi hs hp
  have hd := henergy U hi hs hp
  have hnorm : (∫ t in Iic (1:unitInterval), ‖circleParabolicH4 S τ U t‖^2 ∂volume) =
      ‖circleParabolicH4 S τ U‖^2 :=
    smooth_stability_unit_time_norm_sq (circleParabolicH4 S τ U)
  have hupper := (circle_sobolev_energy_norm_equivalence S V κ hκ.le
    (circleParabolicInitialValue S τ U)).2
  have hscalar : (2*τ*c)*‖circleParabolicH4 S τ U‖^2 ≤
      C*‖circleParabolicInitialValue S τ U‖^2 :=
    (congrArg ((2*τ*c)*·) hnorm.symm).le.trans (hd.trans hupper)
  exact smooth_stability_scalar_h4_bound (2*τ*c) C
    ‖circleParabolicH4 S τ U‖ ‖circleParabolicInitialValue S τ U‖
    hα hC.le (norm_nonneg (circleParabolicH4 S τ U))
      (norm_nonneg (circleParabolicInitialValue S τ U)) hscalar

private theorem smooth_stability_principal_split
    (Q P : C(AddCircle S, ℂ)) (hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1)
    (f : CircleSobolevSpace S 4) :
    circleSobolevPrincipalOperator S f-
      (circleSobolevCoordinate S 2 0+
        circleSobolevLowerOrderOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)))
          (circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)) =
      -(circleNormalGraphDerivative S (circleBernoulliBackground S Q P) (15/2) f) := by
  have hD : circleNormalGraphDerivative S (circleBernoulliBackground S Q P) (15/2) =
      circleSobolevOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) :=
    (circle_normal_graph_hasFDerivAt S (circleBernoulliBackground S Q P) (15/2)).unique
      (bernoulli_sobolev_flow_linearization S Q P hE).2
  rw [hD,circle_sobolev_operator_lower_order]
  have hv : circleSobolevCoordinate S 2 0
      (circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)) =
      circleSobolevCoordinate S 4 0 f := rfl
  simp only [circleSobolevPrincipalOperator,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,hv]
  module

private theorem stability_positive_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ a > 0, P a) (k : ∀ a, 0 < a → P a → Q) : Q := by
  obtain ⟨a,ha,hP⟩ := h
  exact k a ha hP

private theorem stability_two_positive_transport {P : ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ a > 0, ∃ b > 0, P a b)
    (k : ∀ a, 0 < a → ∀ b, 0 < b → P a b → Q) : Q := by
  obtain ⟨a,ha,b,hb,hP⟩ := h
  exact k a ha b hb hP

private theorem stability_two_witness_transport
    {X Y : Type*} {P : X → Y → Prop} {Q : Prop}
    (h : ∃ x, ∃ y, P x y) (k : ∀ x y, P x y → Q) : Q := by
  obtain ⟨x,y,hP⟩ := h
  exact k x y hP

private theorem stability_witness_transport
    {X : Type*} {P : X → Prop} {Q : Prop}
    (h : ∃ x, P x) (k : ∀ x, P x → Q) : Q := by
  obtain ⟨x,hP⟩ := h
  exact k x hP

private theorem smooth_stability_limit_of_time_gate
    {H : Type*} [NormedAddCommGroup H]
    (v : Ioi (0:ℝ) → H) (a τ D x ε C : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (h : ∀ t : Ioi (0:ℝ), (1:ℝ) ≤ (t:ℝ) →
      D*Real.exp (-a*((t:ℝ)-τ))*x < ε →
        ‖v t‖^2 ≤ C*Real.exp (-2*a*(t:ℝ))*x^2) :
    Tendsto v atTop (𝓝 0) := by
  have ht : Tendsto (fun t : Ioi (0:ℝ) => (t:ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hexp (b : ℝ) (hb : 0 < b) :
      Tendsto (fun t : Ioi (0:ℝ) => Real.exp (-b*(t:ℝ))) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (ht.const_mul_atTop hb)
  have hgate : Tendsto (fun t : Ioi (0:ℝ) =>
      D*Real.exp (-a*((t:ℝ)-τ))*x) atTop (𝓝 0) := by
    have hg := ((hexp a ha).const_mul (D*Real.exp (a*τ))).mul_const x
    have hg' : Tendsto (fun t : Ioi (0:ℝ) =>
        (D*Real.exp (a*τ))*Real.exp (-a*(t:ℝ))*x) atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using hg
    apply hg'.congr
    intro t
    calc
      (D*Real.exp (a*τ))*Real.exp (-a*(t:ℝ))*x =
          D*Real.exp (a*τ+(-a*(t:ℝ)))*x := by rw [Real.exp_add]; ring
      _ = D*Real.exp (-a*((t:ℝ)-τ))*x := by congr 2 <;> ring
  have hbound : Tendsto (fun t : Ioi (0:ℝ) =>
      C*Real.exp (-2*a*(t:ℝ))*x^2) atTop (𝓝 0) := by
    have hh := ((hexp (2*a) (by positivity)).const_mul C).mul_const (x^2)
    simpa only [mul_zero,zero_mul,neg_mul,mul_assoc] using hh
  have hevent : ∀ᶠ t : Ioi (0:ℝ) in atTop,
      ‖v t‖^2 ≤ C*Real.exp (-2*a*(t:ℝ))*x^2 := by
    filter_upwards [ht.eventually (eventually_ge_atTop (1:ℝ)),
      hgate.eventually (gt_mem_nhds hε)] with t ht hsmall
    exact h t ht hsmall
  have hsq : Tendsto (fun t : Ioi (0:ℝ) => ‖v t‖^2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun t => sq_nonneg ‖v t‖)) hevent hbound
  have hnorm : Tendsto (fun t : Ioi (0:ℝ) => ‖v t‖) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

private abbrev smoothStabilityConclusion
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Ψ : CircleL2 S)
    (τ : ℝ) (hτ : 0 < τ) (g η : ℝ) : Prop :=
  (∃ ε > 0, ∀ x₀ : CircleSobolevSpace S 2,
    circleSobolevConjugation S 2 x₀ = x₀ →
    inner ℂ Ψ (circleSobolevCoordinate S 2 0 x₀) = 0 → ‖x₀‖ ≤ ε →
    ∃ u : C(ℝ≥0,CircleSobolevSpace S 2), ∃ U : ℕ → CircleParabolicSpace S τ,
      u 0 = x₀ ∧
      (∀ m, ‖U m‖ < η ∧ circleParabolicConjugation S τ (U m) = U m ∧
        ∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ (U m) t =
          circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ (U m) t)) ∧
      (∀ m t, u (circleParabolicSegmentTime τ hτ m t) = circleParabolicCurve S τ (U m) t) ∧
      (∀ t : ℝ≥0, circleSobolevConjugation S 2 (u t) = u t ∧
        inner ℂ Ψ (circleSobolevCoordinate S 2 0 (u t)) = 0) ∧
      ∃ v : ∀ n : ℕ, C(Ioi (0:ℝ),CircleSobolevSpace S n),
        (∀ n (t : Ioi (0:ℝ)), circleSobolevCoordinate S n 0 (v n t) =
          circleSobolevCoordinate S 2 0 (u ⟨(t:ℝ),t.property.le⟩)) ∧
        ∀ n, Tendsto (v n) atTop (𝓝 0)) ∧
  (∀ μ : ℝ, 0 < μ → μ < g → ∀ n : ℕ, ∀ t₀ > 0,
    ∃ ε > 0, ∃ C > 0,
    ∀ (u : C(ℝ≥0,CircleSobolevSpace S 2)) (U : ℕ → CircleParabolicSpace S τ),
      (∀ m t, u (circleParabolicSegmentTime τ hτ m t) = circleParabolicCurve S τ (U m) t) →
      (∀ m, ‖U m‖ < η) →
      (∀ m, ∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ (U m) t =
        circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ (U m) t)) →
      circleSobolevConjugation S 2 (u 0) = u 0 →
      inner ℂ Ψ (circleSobolevCoordinate S 2 0 (u 0)) = 0 →
      ‖u 0‖ ≤ ε →
      ∀ v : C(Ioi (0:ℝ),CircleSobolevSpace S n),
        (∀ t : Ioi (0:ℝ), circleSobolevCoordinate S n 0 (v t) =
          circleSobolevCoordinate S 2 0 (u ⟨(t:ℝ),t.property.le⟩)) →
        ∀ t : Ioi (0:ℝ), t₀ ≤ (t:ℝ) →
          ‖v t‖^2 ≤ C*Real.exp (-2*μ*(t:ℝ))*‖u 0‖^2)

set_option maxHeartbeats 1200000 in
private theorem smooth_stability_of_data
    (Q P : C(AddCircle S, ℂ)) (hQ : HasCircleDeriv S Q P)
    (hP : HasCircleDeriv S P (-(Q^3))) (hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1)
    (Ψ : CircleL2 S) (τ : ℝ) (hτ : 0 < τ)
    (e : CircleParabolicSpace S τ ≃L[ℂ] (CircleSobolevSpace S 2 × CircleTimeL2 S))
    (heInverse : e.toContinuousLinearMap = circleParabolicLowerOrderData S τ
      (circleSobolevCoordinate S 2 0+
        circleSobolevLowerOrderOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))))
    (hpair : inner ℂ Ψ (circleContinuousL2 S (circleBernoulliBackground S Q P).b) ≠ 0)
    (hFzero : circleNormalGraphFlow S (circleBernoulliBackground S Q P) (15/2) 0 = 0)
    (hneutral : ∀ f : CircleSobolevSpace S 4, circleNormalGraphRotationFunctional S Ψ
      (circleNormalGraphDerivative S (circleBernoulliBackground S Q P) (15/2) f) = 0)
    (g : ℝ) (hg : 0 < g) (δU δE A : ℝ) (hδU : 0 < δU)
    (hδE : 0 < δE) (hA : 0 < A)
    (hunique : ∀ U V : CircleParabolicSpace S τ,
      circleParabolicInitialValue S τ U = circleParabolicInitialValue S τ V →
      ‖circleParabolicCurve S τ U‖ < δU → ‖circleParabolicCurve S τ V‖ < δU →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ U t =
        circleNormalGraphModulatedFlow S (circleBernoulliBackground S Q P) (15/2) Ψ
          (circleParabolicH4 S τ U t)) →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ V t =
        circleNormalGraphModulatedFlow S (circleBernoulliBackground S Q P) (15/2) Ψ
          (circleParabolicH4 S τ V t)) → U = V)
    (hH4 : ∀ U : CircleParabolicSpace S τ,
      inner ℂ Ψ (circleSobolevCoordinate S 2 0 (circleParabolicInitialValue S τ U)) = 0 →
      ‖circleParabolicCurve S τ U‖ < δE →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ U t =
        circleNormalGraphModulatedFlow S (circleBernoulliBackground S Q P) (15/2) Ψ
          (circleParabolicH4 S τ U t)) →
      ‖circleParabolicH4 S τ U‖ ≤ A*‖circleParabolicInitialValue S τ U‖)
    (hglobal : ∀ μ : ℝ, 0 < μ → μ < g → ∃ D > 0,
      ∀ η : ℝ, 0 < η → ∃ ε > 0, ∃ r > 0, r < η ∧
        ∀ x₀ : CircleSobolevSpace S 2,
          circleSobolevConjugation S 2 x₀ = x₀ →
          inner ℂ Ψ (circleSobolevCoordinate S 2 0 x₀) = 0 → ‖x₀‖ ≤ ε →
          ∃ u : C(ℝ≥0,CircleSobolevSpace S 2), ∃ U : ℕ → CircleParabolicSpace S τ,
            u 0 = x₀ ∧
            (∀ m, ‖U m‖ ≤ r ∧ circleParabolicConjugation S τ (U m) = U m ∧
              ∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ (U m) t =
                circleNormalGraphModulatedFlow S (circleBernoulliBackground S Q P) (15/2) Ψ
                  (circleParabolicH4 S τ (U m) t)) ∧
            (∀ m t, u (circleParabolicSegmentTime τ hτ m t) = circleParabolicCurve S τ (U m) t) ∧
            (∀ t : ℝ≥0, 0 < t → ∃ (m : ℕ) (s : unitInterval),
              (0:ℝ) < (s:ℝ) ∧ (s:ℝ) < 1 ∧ circleParabolicSegmentTime τ hτ m s = t) ∧
            ∀ t : ℝ≥0, circleSobolevConjugation S 2 (u t) = u t ∧
              inner ℂ Ψ (circleSobolevCoordinate S 2 0 (u t)) = 0 ∧
              ‖u t‖ ≤ D*Real.exp (-μ*(t:ℝ))*‖x₀‖)
    (η_req : ℝ) (hη_req : 0 < η_req) :
    ∃ η > 0, η < η_req ∧
      smoothStabilityConclusion S (circleBernoulliBackground S Q P) Ψ τ hτ g η := by
  refine stability_positive_transport
    (bernoulli_parabolic_global_smoothing S Q P hQ hP hE τ hτ e heInverse
      Ψ hpair hFzero hneutral) ?_
  intro s hs hsm
  let η : ℝ := min (η_req/2) (min s (min δU δE))
  have hη : 0 < η := lt_min (half_pos hη_req) (lt_min hs (lt_min hδU hδE))
  have hηreq : η < η_req := (min_le_left _ _).trans_lt (half_lt_self hη_req)
  have hηs : η ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hηU : η ≤ δU :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hηE : η ≤ δE :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨η,hη,hηreq,?_,?_⟩
  · refine stability_positive_transport (hglobal (g/2) (half_pos hg) (by linarith)) ?_
    intro D hD hsolve
    refine stability_two_positive_transport (hsolve η hη) ?_
    intro ε hε r hr hdata
    refine ⟨ε,hε,?_⟩
    intro x₀ hxreal hxphase hx
    refine stability_two_witness_transport (hdata.2 x₀ hxreal hxphase hx) ?_
    intro u U hsolution
    have hu := hsolution.1
    have hseg := hsolution.2.1
    have hrep := hsolution.2.2.1
    have hbound := hsolution.2.2.2.2
    have hsmall (m : ℕ) : ‖U m‖ < η := (hseg m).1.trans_lt hdata.1
    refine stability_witness_transport (hsm.1 u U hrep
      (fun m => (hsmall m).trans_le hηs) (fun m => (hseg m).2.2)) ?_
    intro v hv
    refine ⟨u,U,hu,(fun m => ⟨hsmall m,(hseg m).2⟩),hrep,
      (fun t => ⟨(hbound t).1,(hbound t).2.1⟩),v,hv,?_⟩
    have hH4U (m : ℕ) : ‖circleParabolicH4 S τ (U m)‖ ≤
        A*‖circleParabolicInitialValue S τ (U m)‖ := by
      have hi : circleParabolicInitialValue S τ (U m) =
          u (circleParabolicSegmentTime τ hτ m 0) := (hrep m 0).symm
      exact hH4 (U m)
        ((congrArg (fun x : CircleSobolevSpace S 2 => inner ℂ Ψ
          (circleSobolevCoordinate S 2 0 x)) hi).trans (hbound _).2.1)
        ((smooth_stability_curve_bound S τ (U m)).trans_lt
          ((hsmall m).trans_le hηE)) (hseg m).2.2
    have hdecay (t : ℝ≥0) : ‖u t‖ ≤ D*Real.exp (-(g/2)*(t:ℝ))*‖u 0‖ := by
      simpa only [hu] using (hbound t).2.2
    intro n
    refine stability_two_positive_transport
      (hsm.2 A hA D hD (g/2) (half_pos hg) n 1 (by norm_num)) ?_
    intro εS hεS C hC hquant
    apply smooth_stability_limit_of_time_gate (v n) (g/2) τ D ‖u 0‖ εS C (half_pos hg) hεS
    intro t ht hgate
    exact hquant u U hrep (fun m => (hsmall m).trans_le hηs)
      (fun m => (hseg m).2.2) hH4U hdecay (v n) (hv n) t ht hgate
  · intro μ hμ hμg n t₀ ht₀
    refine stability_positive_transport (hglobal μ hμ hμg) ?_
    intro D hD hsolve
    refine stability_two_positive_transport (hsolve η hη) ?_
    intro εG hεG r hr hdata
    refine stability_two_positive_transport (hsm.2 A hA D hD μ hμ n t₀ ht₀) ?_
    intro εS hεS C hC hquant
    let ε : ℝ := min εG (εS/(2*(D*Real.exp (μ*τ)+1)))
    have hε : 0 < ε := lt_min hεG (div_pos hεS (by positivity))
    refine ⟨ε,hε,C,hC,?_⟩
    intro u U hrep hsmall hPDE hreal hphase hx v hv t ht
    have hεSle : ε ≤ εS/(2*(D*Real.exp (μ*τ)+1)) := min_le_right _ _
    have hinitial : ‖u 0‖ ≤ εG := hx.trans (min_le_left _ _)
    refine stability_two_witness_transport (hdata.2 (u 0) hreal hphase hinitial) ?_
    intro w W hsolution
    have hw := hsolution.1
    have hsegW := hsolution.2.1
    have hrepW := hsolution.2.2.1
    have hboundW := hsolution.2.2.2.2
    have heq := circle_parabolic_global_uniqueness S τ δU hτ
      (circleNormalGraphModulatedFlow S (circleBernoulliBackground S Q P) (15/2) Ψ)
      hunique u w U W
      (fun m => ⟨(smooth_stability_curve_bound S τ (U m)).trans_lt
        ((hsmall m).trans_le hηU),hPDE m⟩)
      (fun m => ⟨(smooth_stability_curve_bound S τ (W m)).trans_lt
        (((hsegW m).1.trans_lt hdata.1).trans_le hηU),(hsegW m).2.2⟩)
      hrep hrepW hw.symm
    have hdecay (s : ℝ≥0) : ‖u s‖ ≤ D*Real.exp (-μ*(s:ℝ))*‖u 0‖ :=
      (congrArg (fun z : C(ℝ≥0,CircleSobolevSpace S 2) => ‖z s‖) heq.1).le.trans
        (hboundW s).2.2
    have hphaseall (s : ℝ≥0) : inner ℂ Ψ (circleSobolevCoordinate S 2 0 (u s)) = 0 :=
      (congrArg (fun z : C(ℝ≥0,CircleSobolevSpace S 2) =>
        inner ℂ Ψ (circleSobolevCoordinate S 2 0 (z s))) heq.1).trans (hboundW s).2.1
    have hH4U (m : ℕ) : ‖circleParabolicH4 S τ (U m)‖ ≤
        A*‖circleParabolicInitialValue S τ (U m)‖ := by
      have hi : circleParabolicInitialValue S τ (U m) =
          u (circleParabolicSegmentTime τ hτ m 0) := (hrep m 0).symm
      exact hH4 (U m)
        ((congrArg (fun x : CircleSobolevSpace S 2 => inner ℂ Ψ
          (circleSobolevCoordinate S 2 0 x)) hi).trans (hphaseall _))
        ((smooth_stability_curve_bound S τ (U m)).trans_lt
          ((hsmall m).trans_le hηE)) (hPDE m)
    apply hquant u U hrep (fun m => (hsmall m).trans_le hηs) hPDE
      hH4U hdecay v hv t ht
    have hexp : Real.exp (-μ*((t:ℝ)-τ)) ≤ Real.exp (μ*τ) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_nonneg hμ.le t.property.le
      nlinarith only [hm]
    have hscalar : (D*Real.exp (μ*τ))*‖u 0‖ < εS := by
      have hh : ‖u 0‖*(2*(D*Real.exp (μ*τ)+1)) ≤ εS :=
        (le_div_iff₀ (by positivity)).mp (hx.trans hεSle)
      have hn : 0 ≤ (D*Real.exp (μ*τ))*‖u 0‖ := by positivity
      nlinarith only [hh,hn,norm_nonneg (u 0),hεS]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp hD.le) (norm_nonneg _)).trans_lt hscalar

private theorem stability_three_positive_transport
    {P : ℝ → ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ a > 0, ∃ b > 0, ∃ c > 0, P a b c)
    (k : ∀ a, 0 < a → ∀ b, 0 < b → ∀ c, 0 < c → P a b c → Q) : Q := by
  obtain ⟨a,ha,b,hb,c,hc,hP⟩ := h
  exact k a ha b hb c hc hP

private theorem stability_time_transport
    {W : ℝ → Type*} {Q : ∀ τ, W τ → Prop}
    {L Z : ∀ τ : ℝ, 0 < τ → Prop}
    (h : ∃ τ, ∃ hτ : 0 < τ, τ ≤ 1 ∧ ∃ e : W τ, Q τ e ∧ L τ hτ)
    (k : ∀ τ (hτ : 0 < τ), τ ≤ 1 → ∀ e : W τ, Q τ e → L τ hτ → Z τ hτ) :
    ∃ τ, ∃ hτ : 0 < τ, τ ≤ 1 ∧ ∃ e : W τ, Q τ e ∧ Z τ hτ := by
  obtain ⟨τ,hτ,hτ₁,e,he,hL⟩ := h
  exact ⟨τ,hτ,hτ₁,e,he,k τ hτ hτ₁ e he hL⟩

end Data

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

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

set_option maxHeartbeats 1200000 in
/-- On every positive cover the actual real modulated Bernoulli flow has
a global solution converging to zero in every spatial Sobolev norm on one
common initial neighbourhood. The same fixed time and linear inverse
also give, for any smaller spectral rate, uniform quantitative higher-norm
decay of every small global solution with sufficiently small initial data.
No H4 segment estimate, global decay, or smoothing is assumed. -/
theorem bernoulli_cover_parabolic_smooth_stability
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) :
    let Ext := circlePeriodicExtension T S M hS
    let Q := Ext q
    let P := Ext p
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    let K := circleBernoulliBackground S Q P
    let B := circleSobolevCoordinate S 2 0+
      circleSobolevLowerOrderOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))
    let g : ℝ := if M = 1 then 21/4 else 1/(2*(M:ℝ)^2)
    circleConjugate S (Ψ:CircleL2 S) = (Ψ:CircleL2 S) ∧
      inner ℂ (Ψ:CircleL2 S) (circleContinuousL2 S K.b) ≠ 0 ∧
      ∃ τ, ∃ hτ : 0 < τ, τ ≤ 1 ∧
        ∃ e : CircleParabolicSpace S τ ≃L[ℂ] (CircleSobolevSpace S 2 × CircleTimeL2 S),
          e.toContinuousLinearMap = circleParabolicLowerOrderData S τ B ∧
          ∀ η_req > 0, ∃ η > 0, η < η_req ∧
            smoothStabilityConclusion S K (Ψ:CircleL2 S) τ hτ g η := by
  dsimp only
  let Ext := circlePeriodicExtension T S M hS
  let Q := Ext q
  let P := Ext p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let K := circleBernoulliBackground S Q P
  let B := circleSobolevCoordinate S 2 0+
    circleSobolevLowerOrderOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))
  let V : CircleL2 S →L[ℂ] CircleL2 S :=
    (circleCoverStableMetric T S q p hq hp he hqreal hpreal hs hc ho hr
      M hM (ψ:CircleL2 T) hnorm).toContinuousLinearMap
  let g : ℝ := if M = 1 then 21/4 else 1/(2*(M:ℝ)^2)
  have hg : 0 < g := by dsimp only [g]; split_ifs <;> positivity
  have hQ : HasCircleDeriv S Q P := circle_periodic_extension_deriv T S M hS q p hq
  have hP : HasCircleDeriv S P (-(Q^3)) := by
    simpa only [Q,map_neg,map_pow] using
      circle_periodic_extension_deriv T S M hS _ _ hp
  have hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1 :=
    fun x => he (circleCoverProjection T S M hS x)
  have hflow := bernoulli_sobolev_flow_linearization S Q P hE
  have hdata := (paper_periodic_cover_modulated_tame_data T S q p hq hp he
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS).2.2
  have hD : circleNormalGraphDerivative S K (15/2) =
      circleSobolevOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) :=
    (circle_normal_graph_hasFDerivAt S K (15/2)).unique hflow.2
  have hneutral (f : CircleSobolevSpace S 4) :
      circleNormalGraphRotationFunctional S (Ψ:CircleL2 S)
        (circleNormalGraphDerivative S K (15/2) f) = 0 := by
    change inner ℂ (Ψ:CircleL2 S) (circleNormalGraphDerivative S K (15/2) f) = 0
    rw [hD,circle_sobolev_operator_eq_h4]
    exact hdata.2.2.1 (circleSobolevToH4Domain S f)
  have hglobal := bernoulli_cover_modulated_real_global_solution T S q p hq hp he
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS
  have henergy := bernoulli_cover_parabolic_energy_estimate T S q p hq hp he
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS
  dsimp only at hglobal henergy
  refine ⟨hglobal.1,hglobal.2.1,?_⟩
  refine stability_time_transport hglobal.2.2 ?_
  intro τ hτ hτ₁ e heInverse hsolve
  refine stability_two_positive_transport hdata.2.2.2.2.2 ?_
  intro δ₀ hδ₀ C₀ hC₀ htame
  refine stability_positive_transport
    (circle_parabolic_nonlinear_uniqueness S
      (circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S))
      (circleNormalGraphDerivative S K (15/2)) B
      (smooth_stability_principal_split S Q P hE) δ₀ C₀ hδ₀ hC₀.le htame.2) ?_
  intro δU hδU huniq
  refine stability_three_positive_transport
    (henergy (g/2) (half_pos hg) (by linarith)) ?_
  intro κ hκ δE hδE c hc henergyData
  refine stability_positive_transport
    (smooth_stability_h4_from_energy S K (Ψ:CircleL2 S) V κ δE c τ hκ hc hτ
      (fun U hi hs hp => ((henergyData.2 τ hτ U hi hs hp).2 1).2)) ?_
  intro A hA hH4
  intro η_req hη_req
  exact smooth_stability_of_data S Q P hQ hP hE (Ψ:CircleL2 S) τ hτ e heInverse
    hdata.2.1 hflow.1 hneutral g hg δU δE A hδU hδE hA
    (huniq.2 τ hτ) hH4 hsolve η_req hη_req

end Profile
end Lemniscate
