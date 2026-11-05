import Lemniscate.BernoulliParabolicParameterEquation
import Lemniscate.BanachImplicitEquation

/-! A common C-infinity solution branch for the actual translated,
rotating Bernoulli normal-graph equation.  Its time interval and linear
inverse are supplied by the actual local or global construction.  The
same interval and inverse are retained.  The implicit function theorem is
used over the reals, with smoothness order infinity.


-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

private def realLinearEquiv
    {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ G]
    (e : E ≃L[ℂ] G) : E ≃L[ℝ] G where
  toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ
  continuous_toFun := e.continuous
  continuous_invFun := e.symm.continuous

private theorem realLinearEquiv_derivative
    {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ G]
    (e : E ≃L[ℂ] G) {f : E → G} (h : HasFDerivAt f e.toContinuousLinearMap 0) :
    HasFDerivAt f (realLinearEquiv e).toContinuousLinearMap 0 := by
  have hL : (realLinearEquiv e).toContinuousLinearMap =
      e.toContinuousLinearMap.restrictScalars ℝ := by
    ext u
    rfl
  exact hL.symm ▸ h.restrictScalars ℝ

theorem implicit_branch_with_zero_face
    {P E G A : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (F : P × E → G) (S : Set (P × E)) (δ : ℝ) (hδ : 0 < δ)
    (hsmooth : ContDiffOn ℝ ∞ F S)
    (hball : ∀ z : P × E, ‖z‖ < δ → z ∈ S)
    (hzero : F ((0:P),(0:E)) = 0) (e : E ≃L[ℝ] G)
    (hpartial : HasFDerivAt (fun u : E => F (0,u)) e.toContinuousLinearMap 0)
    (face : A → P) (hface : ∀ a, F (face a,0) = 0) :
    ∃ ε > 0, ∃ r > 0, ∃ g : P → E,
      ContDiffOn ℝ ∞ g (Metric.ball 0 ε) ∧
      (∀ p : P, ‖p‖ < ε →
        ‖g p‖ < r ∧ F (p,g p) = 0 ∧
          ∀ u : E, ‖u‖ < r → F (p,u) = 0 → u = g p) ∧
      ∀ a, ‖face a‖ < ε → g (face a) = 0 := by
  have h0 : ((0:P),(0:E)) ∈ Metric.ball (0 : P × E) δ := by
    change dist ((0:P),(0:E)) ((0:P),(0:E)) < δ
    simpa only [dist_self] using hδ
  have hopenBall : IsOpen (Metric.ball (0 : P × E) δ) := Metric.isOpen_ball
  have hsmoothBall : ContDiffOn ℝ ∞ F (Metric.ball (0 : P × E) δ) :=
    hsmooth.mono (fun z hz => hball z
      (by simpa only [Metric.mem_ball,dist_zero_right] using hz))
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hfull := ((hsmoothBall.contDiffAt (hopenBall.mem_nhds h0)).hasStrictFDerivAt hn).hasFDerivAt
  let d := fderiv ℝ F ((0:P),(0:E))
  have hd : HasFDerivAt F d ((0:P),(0:E)) := hfull
  have hcomp := hd.comp (0:E) (ContinuousLinearMap.inr ℝ P E).hasFDerivAt
  have hdeq : d.comp (ContinuousLinearMap.inr ℝ P E) = e.toContinuousLinearMap :=
    hcomp.unique hpartial
  obtain ⟨ε,hε,r,hr,g,_,hgsmooth,hgdata⟩ :=
    banach_implicit_equation F d e (Metric.ball (0 : P × E) δ)
      hopenBall h0 hsmoothBall hzero hd
      (fun u => congrArg (fun L : E →L[ℝ] G => L u) hdeq)
  refine ⟨ε,hε,r,hr,g,hgsmooth,hgdata,?_⟩
  intro a ha
  exact ((hgdata (face a) ha).2.2 0
    (by simpa only [norm_zero] using hr) (hface a)).symm

private theorem implicit_radius_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ δ > 0, P δ) (k : ∀ δ, 0 < δ → P δ → Q) : Q := by
  obtain ⟨δ,hδ,hP⟩ := h
  exact k δ hδ hP

variable (T : ℝ) [Fact (0 < T)]

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
/-- On the time interval of any given actual Bernoulli linear data
inverse, the translated, rotating equation has a common smooth parameter
branch, locally unique in one solution ball and zero on the zero-data face. -/
theorem bernoulli_parabolic_implicit_solution
    (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) (τ : ℝ)
    (e : CircleParabolicSpace T τ ≃L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T))
    (heInverse : e.toContinuousLinearMap = circleParabolicLowerOrderData T τ
      (circleSobolevCoordinate T 2 0+
        circleSobolevLowerOrderOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)))) :
    ∃ ε > 0, ∃ r > 0, ∃ g : CircleParabolicParameter T → CircleParabolicSpace T τ,
      ContDiffOn ℝ ∞ g (Metric.ball 0 ε) ∧
      (∀ z : CircleParabolicParameter T, ‖z‖ < ε →
        ‖g z‖ < r ∧ circleBernoulliParabolicParameterEquation T τ q p (z,g z) = 0 ∧
          ∀ U : CircleParabolicSpace T τ, ‖U‖ < r →
            circleBernoulliParabolicParameterEquation T τ q p (z,U) = 0 → U = g z) ∧
      ∀ a : ℝ, ‖((a,0,0) : CircleParabolicParameter T)‖ < ε → g (a,0,0) = 0 := by
  let K := circleBernoulliBackground T q p
  let D := circleNormalGraphDerivative T K (15/2)
  let B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T :=
    circleSobolevCoordinate T 2 0+
      circleSobolevLowerOrderOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
  have hflow := bernoulli_sobolev_flow_linearization T q p he
  have hD : D = circleSobolevOperator T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) :=
    (circle_normal_graph_hasFDerivAt T K (15/2)).unique hflow.2
  have hBA (f : CircleSobolevSpace T 4) :
      circleSobolevPrincipalOperator T f-
        B (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) = -(D f) := by
    rw [hD,circle_sobolev_operator_lower_order]
    have hvalue : circleSobolevCoordinate T 2 0
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) =
      circleSobolevCoordinate T 4 0 f := rfl
    simp only [circleSobolevPrincipalOperator,B,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,hvalue]
    module
  have hdata := bernoulli_parabolic_parameter_equation T τ q p hq hp he B hBA
  have hpartial : HasFDerivAt
      (fun U : CircleParabolicSpace T τ =>
        circleBernoulliParabolicParameterEquation T τ q p (0,U))
      e.toContinuousLinearMap 0 := by
    simpa only [heInverse] using! hdata.2.2.2.2
  have hpartialR : HasFDerivAt
      (fun U : CircleParabolicSpace T τ =>
        circleBernoulliParabolicParameterEquation T τ q p (0,U))
      (realLinearEquiv e).toContinuousLinearMap 0 := by
    simpa only using! (realLinearEquiv_derivative
      (E := CircleParabolicSpace T τ) (G := CircleSobolevSpace T 2 × CircleTimeL2 T)
      (f := fun U : CircleParabolicSpace T τ =>
        circleBernoulliParabolicParameterEquation T τ q p (0,U)) e hpartial)
  refine implicit_radius_transport
    ((Metric.mem_nhds_iff
      (α := CircleParabolicParameter T × CircleParabolicSpace T τ)
      (x := ((0 : CircleParabolicParameter T),(0 : CircleParabolicSpace T τ)))
      (s := circleBernoulliParabolicParameterDomain T τ q p)).mp
        (by simpa only using! (hdata.1.mem_nhds hdata.2.1))) ?_
  intro δ hδ hball
  have hballNorm (z : CircleParabolicParameter T × CircleParabolicSpace T τ)
      (hz : ‖z‖ < δ) : z ∈ circleBernoulliParabolicParameterDomain T τ q p := by
    apply hball
    change dist z (0 : CircleParabolicParameter T × CircleParabolicSpace T τ) < δ
    exact (dist_zero_right z).trans_lt hz
  exact implicit_branch_with_zero_face
    (circleBernoulliParabolicParameterEquation T τ q p)
    (circleBernoulliParabolicParameterDomain T τ q p)
    δ hδ hdata.2.2.1 hballNorm (hdata.2.2.2.1 0)
    (realLinearEquiv e) hpartialR
    (fun a : ℝ => ((a,0,0) : CircleParabolicParameter T)) hdata.2.2.2.1

end Lemniscate
