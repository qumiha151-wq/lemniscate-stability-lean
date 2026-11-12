import SolitonClassification.Rotating.PolynomialGridAssembly
import SolitonClassification.Rotating.UniversalReducedVariation
import SolitonClassification.Rotating.RotatingGridMarginOrders
import SolitonClassification.Rotating.RotatingGridHorizon

/-! Local order42/order22 bounds for a genuinely extended final segment.
The order22 matrix itself is unchanged; its differential residual here is
against the order42 state polynomial. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set UniversalMajorant
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem shiftedStateResidual42_bound (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t0 t : ℝ}
    (ht : |σ*(t-t0)|≤(universalStepCap:ℝ)) :
    ‖shiftedStateResidual σ a 42 t0 t‖≤(6:ℝ)/10^40 := by
  have hb:=taylorResidual42_uniform ha ht
  rw [polynomial_residual_actual] at hb
  dsimp only [shiftedStateResidual,shiftedPolynomialState]
  rw [norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans (by simpa only [one_mul] using hb)

theorem shiftedMatrixResidual42_22_bound (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) (B : FlowEnd) {t0 t : ℝ}
    (ht : |σ*(t-t0)|≤(universalStepCap:ℝ)) :
    ‖shiftedMatrixResidual σ a 42 22 B t0 t‖≤((2:ℝ)/10^19)*‖B‖ := by
  have hb:=mixedVariationResidualMap_order_norm ha (M:=42) (N:=22)
    (by omega) (by norm_num : (0:ℚ)≤2/10^19) reducedJacobian_budgets.1 ht
  have hb' : ‖mixedVariationResidualMap a 42 22 (σ*(t-t0))‖≤(2:ℝ)/10^19 := by
    norm_num at hb ⊢
    exact hb
  dsimp only [shiftedMatrixResidual]
  rw [norm_smul,Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans
  simp only [one_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right hb' (norm_nonneg B))

theorem shiftedPolynomialMatrix22_bounds (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) (B : FlowEnd) (hB : IsUnit B)
    (hnorm : ‖B‖≤2000) (hinv : ‖Ring.inverse B‖≤4000) {t0 t : ℝ}
    (ht : t-t0∈Icc 0 (universalStepCap:ℝ)) :
    IsUnit (shiftedPolynomialMatrix σ a 22 B t0 t) ∧
      ‖shiftedPolynomialMatrix σ a 22 B t0 t‖≤2400 ∧
      ‖Ring.inverse (shiftedPolynomialMatrix σ a 22 B t0 t)‖≤5000 := by
  have hb:=referencePolynomialMatrix22_bounds σ hσ ha B hB ht
  exact ⟨hb.1,hb.2.1.trans (by linarith),hb.2.2.trans (by linarith)⟩

def extendedReference {V : Type} (F : ℕ → ℝ → V) (N : ℕ) (h r : ℝ)
    (j : ℕ) (t : ℝ) : V := if j<N then F j t else F (N-1) ((N:ℝ)*h+2*r)

theorem extendedReference_before {V : Type} (F : ℕ → ℝ → V)
    {N j : ℕ} (hj : j<N) (h r : ℝ) :
    extendedReference F N h r j=F j := by
  funext t
  simp only [extendedReference,if_pos hj]

theorem extendedReference_terminal {V : Type} (F : ℕ → ℝ → V)
    (N : ℕ) (h r : ℝ) :
    extendedReference F N h r N=fun _=>F (N-1) ((N:ℝ)*h+2*r) := by
  funext t
  simp only [extendedReference,lt_self_iff_false,if_false]

theorem extendedReference_last_reset {V : Type} (F : ℕ → ℝ → V)
    {N : ℕ} (hN : 0<N) (h r : ℝ) :
    extendedReference F N h r (N-1) (extendedGridTime N h r N)=
      extendedReference F N h r N (extendedGridTime N h r N) := by
  rw [extendedReference_before F (by omega : N-1<N),extendedReference_terminal,extendedGridTime_last]

theorem extended_last_local_time {N : ℕ} (hN : 0<N) (h r : ℝ) :
    (N:ℝ)*h+2*r-((N-1:ℕ):ℝ)*h=h+2*r := by
  have hn : ((N-1:ℕ):ℝ)+1=(N:ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
  linear_combination -h*hn

theorem extended_segment_local_cap {N j : ℕ} {h r t : ℝ} (hj : j<N)
    (hr : 0≤r) (hcap : h+2*r≤(universalStepCap:ℝ))
    (ht : t∈Icc (extendedGridTime N h r j) (extendedGridTime N h r (j+1))) :
    t-(j:ℝ)*h∈Icc 0 (universalStepCap:ℝ) :=
  ⟨(extendedGridTime_local_bounds hj hr ht).1,
    (extendedGridTime_local_bounds hj hr ht).2.trans hcap⟩

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Extended order42 references audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Extended order42 references audited: {count} declarations; standard axioms only."
