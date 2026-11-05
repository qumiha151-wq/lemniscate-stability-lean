import Lemniscate.CircleClassicalJetAlgebra
import Lemniscate.NormalGraphCoefficientAlgebra
import Lemniscate.NormalGraphRotation

/-! The actual modulated rational normal-graph field on finite classical
spatial jets. The only inverse conditions concern the value coordinates. -/
noncomputable section
namespace Lemniscate
open Complex Set Filter
open scoped ContDiff Topology

variable (T : ℝ) [Fact (0 < T)] (n : ℕ)

def circleJetRawFlow (K : BackgroundJetOver (CircleClassicalJetAlgebra T n))
    (c : ℝ) (z : Fin 5 → CircleClassicalJetAlgebra T n) :
    CircleClassicalJetAlgebra T n :=
  normalGraphPrincipalCoefficientOver _ K (fun j => z j.castSucc)*z 4 +
    normalGraphLowerOrderCoefficientOver _ K c (fun j => z j.castSucc)

def circleJetRotationField (K : BackgroundJetOver (CircleClassicalJetAlgebra T n))
    (z : Fin 5 → CircleClassicalJetAlgebra T n) : CircleClassicalJetAlgebra T n :=
  K.b+(K.eta+z 0)*z 1*Ring.inverse (1-K.k*z 0)

def circleJetPhaseFunctional (ψ : CircleL2 T) :
    CircleClassicalJetAlgebra T n →L[ℂ] ℂ :=
  (circleNormalGraphRotationFunctional T ψ).comp
    ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).comp
      (circleClassicalJetValueCLM T n))

def circleJetAngularVelocity (K : BackgroundJetOver (CircleClassicalJetAlgebra T n))
    (c : ℝ) (ψ : CircleL2 T) (z : Fin 5 → CircleClassicalJetAlgebra T n) : ℂ :=
  circleJetPhaseFunctional T n ψ (circleJetRawFlow T n K c z) /
    circleJetPhaseFunctional T n ψ (circleJetRotationField T n K z)

def circleJetModulatedFlow (K : BackgroundJetOver (CircleClassicalJetAlgebra T n))
    (c : ℝ) (ψ : CircleL2 T) (z : Fin 5 → CircleClassicalJetAlgebra T n) :
    CircleClassicalJetAlgebra T n :=
  circleJetRawFlow T n K c z -
    circleJetAngularVelocity T n K c ψ z •
      circleJetRotationField T n K z

def circleJetFlowDomain (K : BackgroundJetOver (CircleClassicalJetAlgebra T n))
    (ψ : CircleL2 T) : Set (Fin 5 → CircleClassicalJetAlgebra T n) :=
  {z | (fun j => z j.castSucc) ∈ normalGraphCoefficientDomainOver _ K ∧
    circleJetPhaseFunctional T n ψ (circleJetRotationField T n K z) ≠ 0}

theorem circle_jet_modulated_flow_smooth
    (K : BackgroundJetOver (CircleClassicalJetAlgebra T n)) (c : ℝ)
    (ψ : CircleL2 T) :
    IsOpen (circleJetFlowDomain T n K ψ) ∧
      ContDiffOn ℂ ∞ (circleJetModulatedFlow T n K c ψ)
        (circleJetFlowDomain T n K ψ) ∧
      ContDiffOn ℂ ∞ (circleJetAngularVelocity T n K c ψ)
        (circleJetFlowDomain T n K ψ) := by
  let Z : (Fin 5 → CircleClassicalJetAlgebra T n) →L[ℂ]
      (Fin 4 → CircleClassicalJetAlgebra T n) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.castSucc
  have hZ (w : Fin 5 → CircleClassicalJetAlgebra T n) :
      Z w = fun j => w j.castSucc := rfl
  obtain ⟨hopen,_,hcoeff⟩ :=
    normal_graph_coefficients_smooth_over (CircleClassicalJetAlgebra T n) K c
  have hbaseOpen : IsOpen {z | Z z ∈ normalGraphCoefficientDomainOver _ K} :=
    hopen.preimage Z.continuous
  have hraw (z) (hz : Z z ∈ normalGraphCoefficientDomainOver _ K) :
      ContDiffAt ℂ ∞ (circleJetRawFlow T n K c) z := by
    have h := ((hcoeff (Z z) hz).of_le (show (∞:ℕ∞ω)≤⊤ from le_top)).comp z
      Z.contDiff.contDiffAt
    simpa only [circleJetRawFlow,Function.comp_def,hZ,
      ContinuousLinearMap.proj_apply] using!
      (h.fst.mul (ContinuousLinearMap.proj (4:Fin 5)).contDiff.contDiffAt).add h.snd
  have hrot (z) (hz : Z z ∈ normalGraphCoefficientDomainOver _ K) :
      ContDiffAt ℂ ∞ (circleJetRotationField T n K) z := by
    have hA : ContDiff ℂ ∞ (fun w : Fin 5 → CircleClassicalJetAlgebra T n => 1-K.k*w 0) := by
      fun_prop
    have hi := contDiffAt_ringInverse ℂ (n := (∞:ℕ∞ω)) hz.1.unit
    rw [hz.1.unit_spec] at hi
    have hinv := hi.comp z hA.contDiffAt
    exact contDiffAt_const.add
      (((contDiffAt_const.add (ContinuousLinearMap.proj (0:Fin 5)).contDiff.contDiffAt).mul
        (ContinuousLinearMap.proj (1:Fin 5)).contDiff.contDiffAt).mul hinv)
  have hmod (z) (hz : z ∈ circleJetFlowDomain T n K ψ) :
      ContDiffAt ℂ ∞ (circleJetModulatedFlow T n K c ψ) z ∧
        ContDiffAt ℂ ∞ (circleJetAngularVelocity T n K c ψ) z := by
    have hF := hraw z hz.1
    have hG := hrot z hz.1
    have hnum := (circleJetPhaseFunctional T n ψ).contDiff.contDiffAt.comp z hF
    have hden := (circleJetPhaseFunctional T n ψ).contDiff.contDiffAt.comp z hG
    exact ⟨hF.sub ((hnum.div hden hz.2).smul hG),hnum.div hden hz.2⟩
  refine ⟨?_,fun z hz => (hmod z hz).1.contDiffWithinAt,
    fun z hz => (hmod z hz).2.contDiffWithinAt⟩
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hden := ((circleJetPhaseFunctional T n ψ).continuous.continuousAt.comp
    (hrot z hz.1).continuousAt).eventually_ne hz.2
  filter_upwards [hbaseOpen.mem_nhds hz.1,hden] with w hw hd
  exact ⟨hw,hd⟩

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem circle_jet_modulated_flow_holonomic
    (K : BackgroundJetOver (CircleClassicalJetAlgebra T n)) (c : ℝ)
    (ψ : CircleL2 T) (z : Fin 5 → CircleClassicalJetAlgebra T n)
    (hK : CircleClassicalJetHolonomic T n K.k ∧
      CircleClassicalJetHolonomic T n K.ks ∧
      CircleClassicalJetHolonomic T n K.kss ∧
      CircleClassicalJetHolonomic T n K.ksss ∧
      CircleClassicalJetHolonomic T n K.eta ∧
      CircleClassicalJetHolonomic T n K.b)
    (hz : ∀ j, CircleClassicalJetHolonomic T n (z j))
    (hunit : z ∈ circleJetFlowDomain T n K ψ) :
    CircleClassicalJetHolonomic T n (circleJetModulatedFlow T n K c ψ z) := by
  obtain ⟨hk,hks,hkss,hksss,heta,hb⟩ := hK
  have hA : IsUnit (1-K.k*z 0) := hunit.1.1
  have hH : IsUnit ((1-K.k*z 0)^2+(z 1)^2) := hunit.1.2
  have hc (r : ℝ) : CircleClassicalJetHolonomic T n (algebraMap ℝ _ r) := by
    rw [IsScalarTower.algebraMap_apply ℝ ℂ (CircleClassicalJetAlgebra T n)]
    exact CircleClassicalJetHolonomic.const (T := T) n (r:ℂ)
  have hnat (r : ℕ) : CircleClassicalJetHolonomic T n (r : CircleClassicalJetAlgebra T n) := by
    simpa only [map_natCast] using CircleClassicalJetHolonomic.const (T := T) n (r:ℂ)
  have hone : CircleClassicalJetHolonomic T n (1 : CircleClassicalJetAlgebra T n) := by
    simpa only [map_one] using CircleClassicalJetHolonomic.const (T := T) n (1:ℂ)
  have hzero : CircleClassicalJetHolonomic T n (0 : CircleClassicalJetAlgebra T n) := by
    simpa only [map_zero] using CircleClassicalJetHolonomic.const (T := T) n (0:ℂ)
  dsimp only [circleJetModulatedFlow,circleJetRawFlow,circleJetRotationField,
    normalGraphPrincipalCoefficientOver,normalGraphLowerOrderCoefficientOver,
    normalGraphRationalFlow,graphCurvatureNumeratorSS,graphCurvatureNumeratorS,
    graphCurvatureNumerator,graphMetricSquaredS,graphMetricSquaredSS,
    graphAs,graphAss,graphSupportNumerator,graphA,graphMetricSquared]
  simp only [Algebra.smul_def]
  repeat' first
  | assumption
  | apply CircleClassicalJetHolonomic.add
  | apply CircleClassicalJetHolonomic.sub
  | apply CircleClassicalJetHolonomic.neg
  | apply CircleClassicalJetHolonomic.mul
  | apply CircleClassicalJetHolonomic.pow
  | apply CircleClassicalJetHolonomic.inverse
  | apply CircleClassicalJetHolonomic.const
  | apply hc
  | apply hnat
  | apply hz

end Lemniscate
