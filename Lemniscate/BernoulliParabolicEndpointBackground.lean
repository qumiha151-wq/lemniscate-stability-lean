import Lemniscate.BernoulliParabolicImplicitSolution
import Lemniscate.NormalGraphTranslation

/-! The spatial translation multiplier r+1 is nonzero at the initial
endpoint. Its coefficient path is a fixed continuous pullback of the
already constructed smooth profile shift, without a new profile ODE. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

private theorem endpoint_hasFDerivAt_transport
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f g : E → G) (L M : E →L[ℝ] G) (hfg : f = g) (hLM : L = M)
    (h : HasFDerivAt g M 0) : HasFDerivAt f L 0 := by
  rw [hfg,hLM]
  exact h

private theorem endpoint_restrict_hasFDerivAt
    {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ G]
    (f : E → G) (L : E →L[ℂ] G) (h : HasFDerivAt f L 0) :
    HasFDerivAt f (L.restrictScalars ℝ) 0 := h.restrictScalars ℝ

private theorem endpoint_implicit_radius_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ δ > 0, P δ) (k : ∀ δ, 0 < δ → P δ → Q) : Q := by
  obtain ⟨δ,hδ,hP⟩ := h
  exact k δ hδ hP

private theorem endpoint_implicit_branch_transport
    {P X : Type*} {A : ℝ → ℝ → (P → X) → Prop} {Q : Prop}
    (h : ∃ ε > 0, ∃ r > 0, ∃ g : P → X, A ε r g)
    (k : ∀ ε, 0 < ε → ∀ r, 0 < r → ∀ g : P → X, A ε r g → Q) : Q := by
  obtain ⟨ε,hε,r,hr,g,hA⟩ := h
  exact k ε hε r hr g hA

variable (T : ℝ) [Fact (0 < T)]

private def endpointHalfTime : C(unitInterval,unitInterval) where
  toFun r := ⟨((r:ℝ)+1)/2,⟨by linarith [r.property.1],by linarith [r.property.2]⟩⟩
  continuous_toFun := ((continuous_subtype_val.add_const 1).div_const 2).subtype_mk _

private def endpointTimePullback : C(unitInterval × AddCircle T,unitInterval × AddCircle T) :=
  ⟨fun z => (endpointHalfTime z.1,z.2),
    (endpointHalfTime.continuous.comp continuous_fst).prodMk continuous_snd⟩

private def endpointProfileShift (q : C(AddCircle T,ℂ)) (a : ℝ) :
    CircleTimeCoefficient T :=
  (circleProfileTimeShift T q (2*a)).comp (endpointTimePullback T)

private theorem endpoint_profile_shift_apply (q : C(AddCircle T,ℂ))
    (a : ℝ) (z : unitInterval × AddCircle T) :
    endpointProfileShift T q a z = q (z.2+((a*((z.1:ℝ)+1):ℝ):AddCircle T)) := by
  change q (z.2+(((2*a)*(((z.1:ℝ)+1)/2):ℝ):AddCircle T)) = _
  congr 2
  ring

/-- The actual Bernoulli coefficients translated by x ↦ x+a(r+1). -/
def circleBernoulliParabolicEndpointBackground (q p : C(AddCircle T,ℂ)) (a : ℝ) :
    Fin 6 → CircleTimeCoefficient T :=
  ![(3:ℂ) • endpointProfileShift T q a,
    ((3*Real.sqrt 2:ℝ):ℂ) • endpointProfileShift T p a,
    (-6:ℂ) • (endpointProfileShift T q a)^3,
    ((-18*Real.sqrt 2:ℝ):ℂ) • ((endpointProfileShift T q a)^2*endpointProfileShift T p a),
    -((endpointProfileShift T q a)^3),
    ((Real.sqrt 2:ℝ):ℂ) • (endpointProfileShift T q a*endpointProfileShift T p a)]

theorem bernoulli_parabolic_endpoint_background_slice
    (q p : C(AddCircle T,ℂ)) (a : ℝ) (t : unitInterval) :
    circleTimeNormalGraphBackground T (circleBernoulliParabolicEndpointBackground T q p a) t =
      circleNormalGraphBackgroundTranslation T ((a*((t:ℝ)+1):ℝ):AddCircle T)
        (circleBernoulliBackground T q p) := by
  change BackgroundJetOver.mk _ _ _ _ _ _ = BackgroundJetOver.mk _ _ _ _ _ _
  congr 1 <;> apply ContinuousMap.ext <;> intro x
  all_goals simp only [circleBernoulliParabolicEndpointBackground,circleTimeNormalGraphBackground,
    circleNormalGraphBackgroundTranslation,circleBernoulliBackground,
    Matrix.cons_val_zero',Matrix.cons_val_succ',ContinuousMap.smul_apply,
    ContinuousMap.pow_apply,ContinuousMap.mul_apply,ContinuousMap.neg_apply,
    ContinuousMap.curry_apply]
  all_goals simp [circleCoefficientTranslation,endpoint_profile_shift_apply]

theorem bernoulli_parabolic_endpoint_background_smooth
    (q p : C(AddCircle T,ℂ)) (hq : HasCircleDeriv T q p)
    (hp : HasCircleDeriv T p (-(q^3))) :
    ContDiff ℝ ∞ (circleBernoulliParabolicEndpointBackground T q p) := by
  let L : CircleTimeCoefficient T →L[ℝ] CircleTimeCoefficient T :=
    ContinuousMap.compCLM ℝ ℂ (endpointTimePullback T)
  have hs := circle_profile_time_shift_smooth T q p hq hp
  have hscale : ContDiff ℝ ∞ (fun a : ℝ => 2*a) := contDiff_const.mul contDiff_id
  have hQ : ContDiff ℝ ∞ (endpointProfileShift T q) := L.contDiff.comp (hs.fst.comp hscale)
  have hP : ContDiff ℝ ∞ (endpointProfileShift T p) := L.contDiff.comp (hs.snd.comp hscale)
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp only [circleBernoulliParabolicEndpointBackground,
    Matrix.cons_val_zero',Matrix.cons_val_succ']
  · exact hQ.const_smul (3:ℂ)
  · exact hP.const_smul ((3*Real.sqrt 2:ℝ):ℂ)
  · exact (hQ.pow 3).const_smul (-6:ℂ)
  · exact ((hQ.pow 2).mul hP).const_smul ((-18*Real.sqrt 2:ℝ):ℂ)
  · exact (hQ.pow 3).neg
  · exact (hQ.mul hP).const_smul ((Real.sqrt 2:ℝ):ℂ)

private theorem endpoint_background_zero (q p : C(AddCircle T,ℂ)) :
    circleBernoulliParabolicEndpointBackground T q p 0 =
      circleBernoulliParabolicBackground T q p 0 := by
  funext i
  apply ContinuousMap.ext
  intro z
  fin_cases i <;>
    simp [circleBernoulliParabolicEndpointBackground,circleBernoulliParabolicBackground,
      circleBernoulliBackground,endpoint_profile_shift_apply,circleProfileTimeShift]

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
/-- The endpoint translation equation uses the same actual time interval
and the same linear data inverse as the given solution. The common branch
is smooth without imposing smallness of higher initial derivatives. -/
theorem bernoulli_parabolic_endpoint_implicit_solution
    (q p : C(AddCircle T,ℂ)) (hq : HasCircleDeriv T q p)
    (hp : HasCircleDeriv T p (-(q^3))) (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (τ : ℝ)
    (e : CircleParabolicSpace T τ ≃L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T))
    (heInverse : e.toContinuousLinearMap = circleParabolicLowerOrderData T τ
      (circleSobolevCoordinate T 2 0+
        circleSobolevLowerOrderOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)))) :
    ∃ ε > 0, ∃ r > 0, ∃ g : CircleParabolicParameter T → CircleParabolicSpace T τ,
      ContDiffOn ℝ ∞ g (Metric.ball 0 ε) ∧
      (∀ z : CircleParabolicParameter T, ‖z‖ < ε →
        ‖g z‖ < r ∧
        circleParabolicTranslatedEquation T τ (circleBernoulliParabolicEndpointBackground T q p)
          (z,g z) = 0 ∧
        ∀ U : CircleParabolicSpace T τ, ‖U‖ < r →
          circleParabolicTranslatedEquation T τ (circleBernoulliParabolicEndpointBackground T q p)
            (z,U) = 0 → U = g z) := by
  let b := circleBernoulliParabolicEndpointBackground T q p
  let F := circleParabolicTranslatedEquation T τ b
  let S := circleParabolicTranslatedDomain T τ b
  let B := circleSobolevCoordinate T 2 0+
    circleSobolevLowerOrderOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
  have hflow := bernoulli_sobolev_flow_linearization T q p he
  have hD : circleNormalGraphDerivative T (circleBernoulliBackground T q p) (15/2) =
      circleSobolevOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) :=
    (circle_normal_graph_hasFDerivAt T (circleBernoulliBackground T q p) (15/2)).unique hflow.2
  have hBA (f : CircleSobolevSpace T 4) :
      circleSobolevPrincipalOperator T f-
        B (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) =
          -(circleNormalGraphDerivative T (circleBernoulliBackground T q p) (15/2) f) := by
    rw [hD,circle_sobolev_operator_lower_order]
    have hvalue : circleSobolevCoordinate T 2 0
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) =
      circleSobolevCoordinate T 4 0 f := rfl
    simp only [circleSobolevPrincipalOperator,B,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,hvalue]
    module
  have hdata := bernoulli_parabolic_parameter_equation T τ q p hq hp he B hBA
  have hslice : (fun U : CircleParabolicSpace T τ => F (0,U)) =
      fun U : CircleParabolicSpace T τ => circleBernoulliParabolicParameterEquation T τ q p (0,U) := by
    funext U
    simp only [F,b,circleParabolicTranslatedEquation,circleBernoulliParabolicParameterEquation,
      Prod.fst_zero,endpoint_background_zero]
  let eR : CircleParabolicSpace T τ ≃L[ℝ] (CircleSobolevSpace T 2 × CircleTimeL2 T) :=
    { toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ,
      continuous_toFun := e.continuous,continuous_invFun := e.symm.continuous }
  have hpartial : HasFDerivAt (fun U : CircleParabolicSpace T τ => F (0,U))
      eR.toContinuousLinearMap 0 := by
    have h : HasFDerivAt
        (fun U : CircleParabolicSpace T τ => circleBernoulliParabolicParameterEquation T τ q p (0,U))
        e.toContinuousLinearMap 0 := by simpa only [heInverse] using! hdata.2.2.2.2
    have hL : eR.toContinuousLinearMap = e.toContinuousLinearMap.restrictScalars ℝ := by
      apply ContinuousLinearMap.ext
      intro U
      rfl
    have hR := endpoint_restrict_hasFDerivAt
      (E := CircleParabolicSpace T τ) (G := CircleSobolevSpace T 2 × CircleTimeL2 T)
      (fun U : CircleParabolicSpace T τ => circleBernoulliParabolicParameterEquation T τ q p (0,U))
      e.toContinuousLinearMap h
    exact endpoint_hasFDerivAt_transport
      (fun U : CircleParabolicSpace T τ => F (0,U))
      (fun U : CircleParabolicSpace T τ => circleBernoulliParabolicParameterEquation T τ q p (0,U))
      eR.toContinuousLinearMap (e.toContinuousLinearMap.restrictScalars ℝ)
      hslice hL (by simpa only using! hR)
  have hzero : F ((0:CircleParabolicParameter T),(0:CircleParabolicSpace T τ)) = 0 := by
    rw [show F (0,0) = circleBernoulliParabolicParameterEquation T τ q p (0,0) from
      congrFun hslice 0]
    exact hdata.2.2.2.1 0
  have hreg := circle_parabolic_translated_equation_smooth T τ b
    (bernoulli_parabolic_endpoint_background_smooth T q p hq hp)
  refine endpoint_implicit_radius_transport
    ((Metric.mem_nhds_iff
      (α := CircleParabolicParameter T × CircleParabolicSpace T τ)
      (x := ((0 : CircleParabolicParameter T),(0 : CircleParabolicSpace T τ)))
      (s := S)).mp (by simpa only [S] using! (hreg.1.mem_nhds hreg.2.1))) ?_
  intro δ hδ hball
  have hballNorm (z : CircleParabolicParameter T × CircleParabolicSpace T τ) (hz : ‖z‖ < δ) : z ∈ S := by
    apply hball
    change dist z (0 : CircleParabolicParameter T × CircleParabolicSpace T τ) < δ
    exact (dist_zero_right z).trans_lt hz
  refine endpoint_implicit_branch_transport (implicit_branch_with_zero_face
    F S δ hδ hreg.2.2 hballNorm hzero eR hpartial
    (fun _ : Unit => (0 : CircleParabolicParameter T)) (fun _ => hzero)) ?_
  intro ε hε r hr g hg
  exact ⟨ε,hε,r,hr,g,hg.1,hg.2.1⟩

end Lemniscate
