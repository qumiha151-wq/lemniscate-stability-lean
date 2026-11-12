import SolitonClassification.Rotating.ReferencePolynomialMatrix22
import SolitonClassification.Rotating.RotatingGridMargin
import SolitonClassification.Rotating.FlowBootstrapGridData

/-! Assemble actual finite polynomial references into the noncircular
state/matrix bootstrap interface. Every node inverse and both reset
defects remain explicit inputs. Orders 60 and 22 are kept distinct. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set UniversalMajorant
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def shiftedPolynomialState (σ : ℝ) (a : State) (M : ℕ) (t0 t : ℝ) : State :=
  polynomialPath (taylorPolynomial a M) (σ*(t-t0))
def shiftedPolynomialMatrix (σ : ℝ) (a : State) (N : ℕ) (B : FlowEnd) (t0 t : ℝ) : FlowEnd :=
  referencePolynomialMatrix σ a N B (t-t0)
def shiftedStateResidual (σ : ℝ) (a : State) (M : ℕ) (t0 t : ℝ) : State :=
  σ • (polynomialVelocity (taylorPolynomial a M) (σ*(t-t0))-
    field (shiftedPolynomialState σ a M t0 t))
def shiftedMatrixResidual (σ : ℝ) (a : State) (M N : ℕ) (B : FlowEnd) (t0 t : ℝ) : FlowEnd :=
  σ • ((mixedVariationResidualMap a M N (σ*(t-t0))).comp B)

theorem flowEnd_one_comp (B : FlowEnd) : (1:FlowEnd).comp B=B := one_mul B
theorem flowEnd_comp_one (B : FlowEnd) : B.comp (1:FlowEnd)=B := mul_one B

theorem shiftedPolynomialState_zero (σ : ℝ) (a : State) (M : ℕ) (t0 : ℝ) :
    shiftedPolynomialState σ a M t0 t0=a := by
  simp [shiftedPolynomialState,polynomialPath_taylor_zero]

theorem shiftedPolynomialMatrix_zero (σ : ℝ) (a : State) (N : ℕ) (B : FlowEnd) (t0 : ℝ) :
    shiftedPolynomialMatrix σ a N B t0 t0=B := by
  simp [shiftedPolynomialMatrix,referencePolynomialMatrix,variationPolynomialMap_zero,flowEnd_one_comp]

theorem shiftedPolynomialState_derivative (σ : ℝ) (a : State) (M : ℕ) (t0 t : ℝ) :
    HasDerivAt (shiftedPolynomialState σ a M t0)
      (σ • field (shiftedPolynomialState σ a M t0 t)+shiftedStateResidual σ a M t0 t) t := by
  have h := (signedPolynomial_hasDerivAt σ (taylorPolynomial a M) (t-t0)).scomp t
    ((hasDerivAt_id t).sub_const t0)
  convert! h using 1
  simp only [shiftedStateResidual,smul_sub,one_smul]
  abel

theorem shiftedPolynomialMatrix_derivative (σ : ℝ) (a : State) (M N : ℕ) (B : FlowEnd) (t0 t : ℝ) :
    HasDerivAt (shiftedPolynomialMatrix σ a N B t0)
      ((σ • fderiv ℝ field (shiftedPolynomialState σ a M t0 t))*
        shiftedPolynomialMatrix σ a N B t0 t+shiftedMatrixResidual σ a M N B t0 t) t := by
  have h := (referencePolynomialMatrix_residual_derivative σ a M N B (t-t0)).scomp t
    ((hasDerivAt_id t).sub_const t0)
  convert! h using 1
  simp only [shiftedPolynomialState,shiftedPolynomialMatrix,shiftedMatrixResidual,one_smul]
  ext v i
  rfl

theorem uniform_grid_local_time {h : ℝ} (_hh : 0≤h) (j : ℕ) {t : ℝ}
    (ht : t∈Icc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h)) : t-(j:ℝ)*h∈Icc 0 h := by
  constructor
  · linarith [ht.1]
  · push_cast at ht
    nlinarith [ht.2]

def polynomialGrid60_22 (σ : ℝ) (hσ : |σ|≤1) (N : ℕ) (h R δX δM : ℝ)
    (a : ℕ → State) (B : ℕ → FlowEnd)
    (hh : 0≤h) (hcap : h≤(universalStepCap:ℝ)) (hR : 3*R≤1/100)
    (ha : ∀j<N,a j∈innerTube) (hB0 : B 0=1)
    (hunit : ∀j≤N,IsUnit (B j)) (hB : ∀j≤N,‖B j‖≤2)
    (hinv : ∀j≤N,‖Ring.inverse (B j)‖≤2)
    (hδX : 0≤δX) (hδM : 0≤δM)
    (hresetX : ∀j<N,‖polynomialPath (taylorPolynomial (a j) 60) (σ*h)-a (j+1)‖≤δX)
    (hresetM : ∀j<N,‖referencePolynomialMatrix σ (a j) 22 (B j) h-B (j+1)‖≤δM) :
    FlowBootstrapGridData σ N ((N:ℝ)*h) 3 3 R (4/10^19) (1/10^57) where
  time j := (j:ℝ)*h
  matrix j := shiftedPolynomialMatrix σ (a j) 22 (B j) ((j:ℝ)*h)
  reference j := shiftedPolynomialState σ (a j) 60 ((j:ℝ)*h)
  matrixResidual j := shiftedMatrixResidual σ (a j) 60 22 (B j) ((j:ℝ)*h)
  stateResidual j := shiftedStateResidual σ (a j) 60 ((j:ℝ)*h)
  matrixJump _ := δM
  stateJump _ := δX
  timeZero := by simp
  timeLast := rfl
  timeMem j hj := ⟨mul_nonneg (Nat.cast_nonneg _) hh,mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh⟩
  timeStep j _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hh
  matrixInitial := by simpa only [Nat.cast_zero,zero_mul,shiftedPolynomialMatrix_zero] using hB0
  nodeUnit j hj := by simpa only [shiftedPolynomialMatrix_zero] using hunit j hj
  nodeInverseBound j hj := by
    simpa only [shiftedPolynomialMatrix_zero] using (hinv j hj).trans (by norm_num : (2:ℝ)≤3)
  matrixContinuous j _ :=
    (continuous_iff_continuousAt.mpr (fun t=>(shiftedPolynomialMatrix_derivative σ (a j) 60 22 (B j) ((j:ℝ)*h) t).continuousAt)).continuousOn
  referenceContinuous j _ :=
    (continuous_iff_continuousAt.mpr (fun t=>(shiftedPolynomialState_derivative σ (a j) 60 ((j:ℝ)*h) t).continuousAt)).continuousOn
  matrixUnit j hj t ht := by
    have hs:=uniform_grid_local_time hh j ht
    exact (referencePolynomialMatrix22_bounds σ hσ (ha j hj) (B j) (hunit j (by omega))
      ⟨hs.1,hs.2.trans hcap⟩).1
  matrixDerivative j _ t _ := (shiftedPolynomialMatrix_derivative σ (a j) 60 22 (B j) ((j:ℝ)*h) t).hasDerivWithinAt
  referenceDerivative j _ t _ := (shiftedPolynomialState_derivative σ (a j) 60 ((j:ℝ)*h) t).hasDerivWithinAt
  matrixBound j hj t ht := by
    have hs:=uniform_grid_local_time hh j ht
    have hb:=(referencePolynomialMatrix22_bounds σ hσ (ha j hj) (B j) (hunit j (by omega))
      ⟨hs.1,hs.2.trans hcap⟩).2.1
    exact hb.trans (by linarith [hB j (by omega)])
  inverseBound j hj t ht := by
    have hs:=uniform_grid_local_time hh j ht
    have hb:=(referencePolynomialMatrix22_bounds σ hσ (ha j hj) (B j) (hunit j (by omega))
      ⟨hs.1,hs.2.trans hcap⟩).2.2
    exact hb.trans (by linarith [hinv j (by omega)])
  matrixResidualBound j hj t ht := by
    have hs:=uniform_grid_local_time hh j ht
    have hb:=referencePolynomialMatrix22_residual_norm σ hσ (ha j hj) (B j) ⟨hs.1,hs.2.trans hcap⟩
    exact hb.trans (by nlinarith [hB j (by omega)])
  stateResidualBound j hj t ht := by
    have hs:=uniform_grid_local_time hh j ht
    have ht' : |σ*(t-(j:ℝ)*h)|≤(universalStepCap:ℝ) := by
      rw [abs_mul,abs_of_nonneg hs.1]
      exact (mul_le_mul_of_nonneg_right hσ hs.1).trans (by simpa using hs.2.trans hcap)
    have hb:=actual_velocity_residual60_uniform (ha j hj) ht'
    dsimp only [shiftedStateResidual,shiftedPolynomialState]
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans (by simpa using hb)
  referenceMargin j hj t ht := by
    apply taylorPolynomial60_bootstrap_margin (ha j hj) hR
    have hs:=uniform_grid_local_time hh j ht
    rw [abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_right hσ hs.1).trans (by simpa using hs.2.trans hcap)
  matrixJumpNonneg _ _ := hδM
  stateJumpNonneg _ _ := hδX
  matrixReset j hj := by
    have he : (((j+1:ℕ):ℝ)*h)-(j:ℝ)*h=h := by push_cast; ring
    simpa only [shiftedPolynomialMatrix,he,sub_self,referencePolynomialMatrix,mul_zero,
      variationPolynomialMap_zero,flowEnd_one_comp] using hresetM j hj
  stateReset j hj := by
    have he : (((j+1:ℕ):ℝ)*h)-(j:ℝ)*h=h := by push_cast; ring
    simpa only [shiftedPolynomialState,he,sub_self,mul_zero,polynomialPath_taylor_zero] using hresetX j hj

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.polynomialGrid60_22
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Actual polynomial reference-grid assembly audited."
