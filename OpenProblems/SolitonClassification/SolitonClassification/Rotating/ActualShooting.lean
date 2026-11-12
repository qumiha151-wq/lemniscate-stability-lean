import SolitonClassification.Rotating.FlowJoint
import SolitonClassification.Rotating.ShootingRoot

/-! The shooting map now uses a proved existing actual flow. Joint strict
differentiability follows from actual tube confinement via FlowJoint; it is
not a free assumption about an unspecified flow. Numeric/Hessian bounds are
still separate obligations. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Metric
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

theorem supportFlow_reflection (σ : ℝ) (hσ : |σ|≤1) (t : ℝ) (a : State) :
    supportFlow σ hσ (-t) a=supportFlow (-σ) (by simpa using hσ) t a := by
  have he : (fun s => supportFlow σ hσ (-s) a)=
      fun s => supportFlow (-σ) (by simpa using hσ) s a := by
    apply supportFlow_unique (-σ) (by simpa using hσ)
    · simp only [neg_zero,supportFlow_zero]
    · intro s
      have hd := (supportFlow_derivative σ hσ a (-s)).scomp s (hasDerivAt_neg s)
      convert! hd using 1
      simp only [signedClippedField]
      module
  exact congrFun he t

def actualFlow (p : ℝ×State) : State := supportFlow 1 (by norm_num) p.1 p.2

def timeReflection : (ℝ×State) →L[ℝ] (ℝ×State) :=
  (-ContinuousLinearMap.fst ℝ ℝ State).prod (ContinuousLinearMap.snd ℝ ℝ State)

theorem actualFlow_reflected (p : ℝ×State) :
    actualFlow p=supportFlow (-1) (by norm_num) (-p.1) p.2 := by
  have h := supportFlow_reflection 1 (by norm_num) (-p.1) p.2
  simpa only [neg_neg,actualFlow] using h

def actualFlowDifferential (p : ℝ×State) : (ℝ×State) →L[ℝ] State :=
  if p.1<0 then
    (supportFlowDifferential (-1) (by norm_num) (timeReflection p)).comp timeReflection
  else supportFlowDifferential 1 (by norm_num) p

theorem actualFlow_hasStrictFDerivAt_positive (T : ℝ) {c : State} {R : ℝ}
    (hR : 0<R) (hreg : FlowTubeNeighborhood 1 (by norm_num) T c R)
    {p : ℝ×State} (hp : p∈Ioo 0 T ×ˢ Metric.ball c (R/4)) :
    HasStrictFDerivAt actualFlow (actualFlowDifferential p) p := by
  rw [actualFlowDifferential,if_neg (not_lt.mpr hp.1.1.le)]
  exact supportFlow_hasStrictFDerivAt_joint 1 (by norm_num) T hR hreg hp

theorem actualFlow_hasStrictFDerivAt_negative (T : ℝ) {c : State} {R : ℝ}
    (hR : 0<R) (hreg : FlowTubeNeighborhood (-1) (by norm_num) T c R)
    {p : ℝ×State} (hp : -p.1∈Ioo 0 T ∧ p.2∈Metric.ball c (R/4)) :
    HasStrictFDerivAt actualFlow (actualFlowDifferential p) p := by
  have hpt : p.1<0 := by linarith [hp.1.1]
  rw [actualFlowDifferential,if_pos hpt]
  have hD := (supportFlow_hasStrictFDerivAt_joint (-1) (by norm_num) T hR hreg
    (p:=timeReflection p) hp).comp p timeReflection.hasStrictFDerivAt
  convert! hD using 1
  funext q
  exact actualFlow_reflected q

def actualShootingMap (e : Fin 2 → ℝ) : Parameters → Parameters := shootingMap e actualFlow
def actualShootingDerivative (e : Fin 2 → ℝ) : Parameters → Parameters →L[ℝ] Parameters :=
  shootingDerivative e actualFlowDifferential

/-- The exact five-parameter map, with its actual positive/negative ODE
endpoint values, is strictly differentiable. The sole analytic region input
is actual confinement of the two chosen flow families. -/
theorem actualShootingMap_hasStrictFDerivAt (e : Fin 2 → ℝ) (T : ℝ)
    {c : State} {R : ℝ} (hR : 0<R)
    (hplus : FlowTubeNeighborhood 1 (by norm_num) T c R)
    (hminus : FlowTubeNeighborhood (-1) (by norm_num) T c R)
    {p : Parameters} (hlength : p 2∈Ioo 0 T)
    (hinitial : shootingInitial e p∈Metric.ball c (R/4)) :
    HasStrictFDerivAt (actualShootingMap e) (actualShootingDerivative e p) p := by
  apply shootingMap_hasStrictFDerivAt
  · exact actualFlow_hasStrictFDerivAt_positive T hR hplus ⟨hlength,hinitial⟩
  · apply actualFlow_hasStrictFDerivAt_negative T hR hminus
    constructor
    · simpa only [backwardEndpointInput,ContinuousLinearMap.prod_apply,
        neg_apply,shootingLength,ContinuousLinearMap.proj_apply,neg_neg]
        using hlength
    · exact hinitial

/-- An actual-root theorem requiring no assumed flow C1 property. The
remaining derivative/residual certificates must still be proved for these
actual functions before this can assert the rotating candidate's root. -/
theorem exists_unique_actual_shooting_zero (e : Fin 2 → ℝ) (T : ℝ)
    {c : State} {R : ℝ} (hR : 0<R)
    (hplus : FlowTubeNeighborhood 1 (by norm_num) T c R)
    (hminus : FlowTubeNeighborhood (-1) (by norm_num) T c R)
    (B J : Parameters →L[ℝ] Parameters) (p y : Parameters)
    {r η ε β H q₀ ζ : ℝ} (q : ℝ≥0)
    (hr : 0≤r) (hβ : 0≤β) (hH : 0≤H) (hq : q<1) (hq₀ : q₀<1)
    (hdomain : ∀a∈closedBall p r,a 2∈Ioo 0 T ∧ shootingInitial e a∈Metric.ball c (R/4))
    (hvariation : ∀a∈closedBall p r,
      ‖actualShootingDerivative e a-actualShootingDerivative e p‖≤H*dist a p)
    (hzero : ‖y-actualShootingMap e p‖≤η)
    (hJ : ‖J-actualShootingDerivative e p‖≤ε) (hB : ‖B‖≤β)
    (hmatrix : ‖ContinuousLinearMap.id ℝ Parameters-B.comp J‖≤q₀)
    (hresidual : ‖B y‖≤ζ) (hcontraction : q₀+β*(ε+H*r)≤(q:ℝ))
    (hself : (ζ+β*η)+(q:ℝ)*r≤r) :
    ∃a∈closedBall p r,actualShootingMap e a=0 ∧
      ∀a'∈closedBall p r,actualShootingMap e a'=0 → a'=a :=
  exists_unique_zero_of_strict_certificate (actualShootingMap e) (actualShootingDerivative e)
    B J p y q hr hβ hH hq hq₀
    (fun a ha => actualShootingMap_hasStrictFDerivAt e T hR hplus hminus
      (hdomain a ha).1 (hdomain a ha).2)
    hvariation hzero hJ hB hmatrix hresidual hcontraction hself

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual-shooting audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual-shooting audit passed for {count} declarations."
