module

public import SolitonClassification.Rotating.FlowInverse
public import SolitonClassification.Rotating.ActualRootFromMatrices

@[expose] public section

/-! The actual-root bridge with canonical inverse. The remaining matrix
premises are bounds for the actual derivative and its actual canonical
inverse. Invertibility and inverse continuity are proved analytically. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Metric
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

structure ActualFlowMatrixBounds (σ : ℝ) (hσ : |σ|≤1)
    (T : ℝ) (c : State) (R : ℝ) (S : Set State) (K I : ℝ) : Prop where
  tube : FlowTubeNeighborhood σ hσ T c R
  derivativeBound : ∀a∈S,∀t∈Icc 0 T,
    ‖fderiv ℝ (supportFlow σ hσ t) a‖≤K
  inverseBound : ∀a∈S,∀t∈Icc 0 T,‖supportFlowInverse σ hσ a t‖≤I

def ActualFlowMatrixBounds.toTrueCertificate {σ : ℝ} {hσ : |σ|≤1}
    {T : ℝ} {c : State} {R K I : ℝ} {S : Set State}
    (h : ActualFlowMatrixBounds σ hσ T c R S K I) (hsub : S⊆ball c R) :
    TrueFlowMatrixCertificate σ hσ T c R S K I where
  tube := h.tube
  derivativeBound := h.derivativeBound
  inverse := supportFlowInverse σ hσ
  inverseContinuous := fun _a ha => supportFlow_inverse_continuousOn σ hσ h.tube (hsub ha)
  inverseIdentity := fun _a ha _t ht => supportFlow_fderiv_comp_inverse σ hσ h.tube (hsub ha) ht
  inverseBound := h.inverseBound

theorem exists_unique_actual_shooting_zero_of_actual_matrix_bounds
    (e : Fin 2 → ℝ) (he0 : |e 0|≤1) (he1 : |e 1|≤1)
    {T : ℝ} (hT : 0≤T) {c : State} {R K I : ℝ} {S : Set State}
    (hR : 0<R) (hK : 0≤K) (hI : 0≤I)
    (hS : Convex ℝ S) (hsub : S⊆ball c (R/4))
    (plus : ActualFlowMatrixBounds 1 (by norm_num) T c R S K I)
    (minus : ActualFlowMatrixBounds (-1) (by norm_num) T c R S K I)
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
  have hsub' : S⊆ball c R := by
    intro a ha
    have hh := hsub ha
    change dist a c<R/4 at hh
    change dist a c<R
    linarith
  exact exists_unique_actual_shooting_zero_of_true_matrices e he0 he1 hT hR hK hI hS hsub
    (plus.toTrueCertificate hsub') (minus.toTrueCertificate hsub') B J p y q
    hr hβ hq hq₀ hdomain hzero hJ hB hmatrix hresidual hcontraction hself

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating canonical-inverse root audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating canonical-inverse root audit passed for {count} declarations."
