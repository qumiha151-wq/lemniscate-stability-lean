module

public import SolitonClassification.Rotating.ShootingVariation

@[expose] public section

/-! A root bridge for the actual rotating ODE. The analytic inputs are
actual tube confinement and actual fundamental/inverse matrix bounds.
Neither flow differentiability, a shooting Hessian, nor shooting derivative
variation is an assumption. Numerical center enclosures remain explicit.
-/
namespace SolitonClassification.Rotating
noncomputable section
open Set Metric
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

/-- These statements concern the derivative of the proved existing flow,
not a polynomial approximation or an independently specified matrix. -/
structure TrueFlowMatrixCertificate (σ : ℝ) (hσ : |σ|≤1)
    (T : ℝ) (c : State) (R : ℝ) (S : Set State) (K I : ℝ) where
  tube : FlowTubeNeighborhood σ hσ T c R
  derivativeBound : ∀a∈S,∀t∈Icc 0 T,
    ‖fderiv ℝ (supportFlow σ hσ t) a‖≤K
  inverse : State → ℝ → State →L[ℝ] State
  inverseContinuous : ∀a∈S,ContinuousOn (inverse a) (Icc 0 T)
  inverseIdentity : ∀a∈S,∀t∈Icc 0 T,
    (fderiv ℝ (supportFlow σ hσ t) a).comp (inverse a t)=
      ContinuousLinearMap.id ℝ State
  inverseBound : ∀a∈S,∀t∈Icc 0 T,‖inverse a t‖≤I

theorem exists_unique_actual_shooting_zero_of_true_matrices
    (e : Fin 2 → ℝ) (he0 : |e 0|≤1) (he1 : |e 1|≤1)
    {T : ℝ} (hT : 0≤T) {c : State} {R K I : ℝ} {S : Set State}
    (hR : 0<R) (hK : 0≤K) (hI : 0≤I)
    (hS : Convex ℝ S) (hsub : S⊆ball c (R/4))
    (plus : TrueFlowMatrixCertificate 1 (by norm_num) T c R S K I)
    (minus : TrueFlowMatrixCertificate (-1) (by norm_num) T c R S K I)
    (B J : Parameters →L[ℝ] Parameters) (p y : Parameters)
    {r η ε β q₀ ζ : ℝ} (q : ℝ≥0)
    (hr : 0≤r) (hβ : 0≤β) (hq : q<1) (hq₀ : q₀<1)
    (hdomain : ∀a∈closedBall p r,a 2∈Ioo 0 T ∧ shootingInitial e a∈S)
    (hzero : ‖y-actualShootingMap e p‖≤η)
    (hJ : ‖J-actualShootingDerivative e p‖≤ε) (hB : ‖B‖≤β)
    (hmatrix : ‖ContinuousLinearMap.id ℝ Parameters-B.comp J‖≤q₀)
    (hresidual : ‖B y‖≤ζ)
    (hcontraction : q₀+β*(ε+(16*trueJointVariationBudget T K I)*r)≤(q:ℝ))
    (hself : (ζ+β*η)+(q:ℝ)*r≤r) :
    ∃a∈closedBall p r,actualShootingMap e a=0 ∧
      ∀a'∈closedBall p r,actualShootingMap e a'=0 → a'=a := by
  have hbudget : 0≤16*trueJointVariationBudget T K I := by
    dsimp [trueJointVariationBudget]
    positivity
  apply exists_unique_actual_shooting_zero e T hR plus.tube minus.tube B J p y q
    hr hβ hbudget hq hq₀
  · intro a ha
    exact ⟨(hdomain a ha).1,hsub (hdomain a ha).2⟩
  · intro a ha
    exact actualShootingDerivative_sharp_variation e he0 he1 hT hR hK hI
      plus.tube minus.tube hS hsub plus.derivativeBound minus.derivativeBound
      plus.inverse minus.inverse plus.inverseContinuous minus.inverseContinuous
      plus.inverseIdentity minus.inverseIdentity plus.inverseBound minus.inverseBound
      (hdomain a ha) (hdomain p (mem_closedBall_self hr))
  · exact hzero
  · exact hJ
  · exact hB
  · exact hmatrix
  · exact hresidual
  · exact hcontraction
  · exact hself

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual-matrix root audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual-matrix root audit passed for {count} declarations."
