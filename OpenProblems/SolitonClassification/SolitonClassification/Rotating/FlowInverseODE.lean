import SolitonClassification.Rotating.FlowInverse
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The canonical actual inverse satisfies its actual inverse variational
ODE. This supports comparison with numerical inverse-matrix polynomials. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem supportFlow_inverse_zero (σ : ℝ) (hσ : |σ|≤1) (a : State) :
    supportFlowInverse σ hσ a 0=ContinuousLinearMap.id ℝ State := by
  change Ring.inverse (fderiv ℝ (supportFlow σ hσ 0) a)=1
  rw [supportFlow_fderiv_initial]
  exact Ring.inverse_one (State →L[ℝ] State)

theorem supportFlow_inverse_hasDerivWithinAt (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Ico 0 T) :
    HasDerivWithinAt (supportFlowInverse σ hσ a)
      (-(supportFlowInverse σ hσ a t).comp (flowLinearCoefficient σ hσ a t)) (Ici t) t := by
  let P := fderiv ℝ (supportFlow σ hσ t) a
  let Q := supportFlowInverse σ hσ a t
  let A := flowLinearCoefficient σ hσ a t
  obtain ⟨u,hu⟩ := supportFlow_fderiv_isUnit σ hσ hreg ha (Ico_subset_Icc_self ht)
  have hi : (↑u⁻¹ : State →L[ℝ] State)=Q := by
    rw [←Ring.inverse_unit,hu]
    rfl
  have hdi := hasFDerivAt_ringInverse (𝕜:=ℝ) u
  rw [hu] at hdi
  have hd := hdi.comp_hasDerivWithinAt t (supportFlow_fderiv_hasDerivWithinAt σ hσ hreg ha ht)
  have hPQ : P*Q=1 := supportFlow_fderiv_comp_inverse σ hσ hreg ha (Ico_subset_Icc_self ht)
  convert! hd using 1
  simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply,hi]
  change -(Q*A)=-(Q*(A*P)*Q)
  rw [mul_assoc,mul_assoc,hPQ,mul_one]

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual inverse ODE audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual inverse ODE audit passed for {count} declarations."
