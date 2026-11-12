import SolitonClassification.Rotating.ExtendedPolynomialReference42

/-! A complete extended reference grid. Its final node is the final segment's
own value at the extended endpoint, held constant as a function of time.
Thus the final reset is exactly zero. Only internal resets are inputs. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set UniversalMajorant
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def extendedPolynomialState42 (σ : ℝ) (a : ℕ → State) (N : ℕ) (h r : ℝ) : ℕ → ℝ → State :=
  extendedReference (fun j=>shiftedPolynomialState σ (a j) 42 ((j:ℝ)*h)) N h r

def extendedPolynomialMatrix22 (σ : ℝ) (a : ℕ → State) (B : ℕ → FlowEnd)
    (N : ℕ) (h r : ℝ) : ℕ → ℝ → FlowEnd :=
  extendedReference (fun j=>shiftedPolynomialMatrix σ (a j) 22 (B j) ((j:ℝ)*h)) N h r

theorem extendedPolynomialState42_before (σ : ℝ) (a : ℕ → State)
    {N j : ℕ} (hj : j<N) (h r : ℝ) :
    extendedPolynomialState42 σ a N h r j=shiftedPolynomialState σ (a j) 42 ((j:ℝ)*h) :=
  extendedReference_before _ hj h r

theorem extendedPolynomialMatrix22_before (σ : ℝ) (a : ℕ → State) (B : ℕ → FlowEnd)
    {N j : ℕ} (hj : j<N) (h r : ℝ) :
    extendedPolynomialMatrix22 σ a B N h r j=shiftedPolynomialMatrix σ (a j) 22 (B j) ((j:ℝ)*h) :=
  extendedReference_before _ hj h r

theorem extendedPolynomialMatrix22_node_bounds (σ : ℝ) (hσ : |σ|≤1)
    {N : ℕ} (hN : 0<N) {h r : ℝ} (hh : 0≤h) (hr : 0≤r)
    (hcap : h+2*r≤(universalStepCap:ℝ)) (a : ℕ → State) (B : ℕ → FlowEnd)
    (ha : ∀j<N,a j∈innerTube) (hunit : ∀j<N,IsUnit (B j))
    (hB : ∀j<N,‖B j‖≤2000) (hinv : ∀j<N,‖Ring.inverse (B j)‖≤4000)
    {j : ℕ} (hj : j≤N) :
    IsUnit (extendedPolynomialMatrix22 σ a B N h r j (extendedGridTime N h r j)) ∧
      ‖extendedPolynomialMatrix22 σ a B N h r j (extendedGridTime N h r j)‖≤2400 ∧
      ‖Ring.inverse (extendedPolynomialMatrix22 σ a B N h r j (extendedGridTime N h r j))‖≤5000 := by
  by_cases hj' : j<N
  · rw [extendedPolynomialMatrix22_before σ a B hj',extendedGridTime_before hj']
    exact shiftedPolynomialMatrix22_bounds σ hσ (ha j hj') (B j) (hunit j hj') (hB j hj') (hinv j hj')
      (by simpa only [sub_self] using (show (0:ℝ)∈Icc 0 (universalStepCap:ℝ) from
        ⟨le_rfl,universalStepCap_pos.le⟩))
  · have he : j=N := by omega
    subst j
    rw [extendedPolynomialMatrix22,extendedReference_terminal]
    apply shiftedPolynomialMatrix22_bounds σ hσ (ha (N-1) (by omega)) (B (N-1))
      (hunit (N-1) (by omega)) (hB (N-1) (by omega)) (hinv (N-1) (by omega))
    rw [extended_last_local_time hN]
    exact ⟨by positivity,hcap⟩

def extendedPolynomialGrid42 (σ : ℝ) (hσ : |σ|≤1) (N : ℕ) (hN : 0<N)
    (h r R : ℝ) (a : ℕ → State) (B : ℕ → FlowEnd) (δX δM : ℕ → ℝ)
    (hh : 0≤h) (hr : 0≤r) (hcap : h+2*r≤(universalStepCap:ℝ)) (hR : 2400*R≤1/100)
    (ha : ∀j<N,a j∈innerTube) (hB0 : B 0=1)
    (hunit : ∀j<N,IsUnit (B j)) (hB : ∀j<N,‖B j‖≤2000)
    (hinv : ∀j<N,‖Ring.inverse (B j)‖≤4000)
    (hδX : ∀j,j+1<N→0≤δX j) (hδM : ∀j,j+1<N→0≤δM j)
    (hresetX : ∀j,j+1<N→‖polynomialPath (taylorPolynomial (a j) 42) (σ*h)-a (j+1)‖≤δX j)
    (hresetM : ∀j,j+1<N→‖referencePolynomialMatrix σ (a j) 22 (B j) h-B (j+1)‖≤δM j) :
    FlowBootstrapGridData σ N ((N:ℝ)*h+2*r) 2400 5000 R (4/10^16) (6/10^40) where
  time := extendedGridTime N h r
  matrix := extendedPolynomialMatrix22 σ a B N h r
  reference := extendedPolynomialState42 σ a N h r
  matrixResidual j t := if j<N then shiftedMatrixResidual σ (a j) 42 22 (B j) ((j:ℝ)*h) t else 0
  stateResidual j t := if j<N then shiftedStateResidual σ (a j) 42 ((j:ℝ)*h) t else 0
  matrixJump j := if j+1<N then δM j else 0
  stateJump j := if j+1<N then δX j else 0
  timeZero := extendedGridTime_zero hN h r
  timeLast := extendedGridTime_last N h r
  timeMem _ hj := extendedGridTime_mem hj hh hr
  timeStep _ hj := extendedGridTime_step hj hh hr
  matrixInitial := by
    rw [extendedPolynomialMatrix22_before σ a B hN]
    simpa only [Nat.cast_zero,zero_mul,shiftedPolynomialMatrix_zero] using hB0
  nodeUnit j hj := (extendedPolynomialMatrix22_node_bounds σ hσ hN hh hr hcap a B ha hunit hB hinv hj).1
  nodeInverseBound j hj := (extendedPolynomialMatrix22_node_bounds σ hσ hN hh hr hcap a B ha hunit hB hinv hj).2.2
  matrixContinuous j hj := by
    rw [extendedPolynomialMatrix22_before σ a B hj]
    exact (continuous_iff_continuousAt.mpr (fun t=>
      (shiftedPolynomialMatrix_derivative σ (a j) 42 22 (B j) ((j:ℝ)*h) t).continuousAt)).continuousOn
  referenceContinuous j hj := by
    rw [extendedPolynomialState42_before σ a hj]
    exact (continuous_iff_continuousAt.mpr (fun t=>
      (shiftedPolynomialState_derivative σ (a j) 42 ((j:ℝ)*h) t).continuousAt)).continuousOn
  matrixUnit j hj t ht := by
    rw [extendedPolynomialMatrix22_before σ a B hj]
    exact (shiftedPolynomialMatrix22_bounds σ hσ (ha j hj) (B j) (hunit j hj) (hB j hj) (hinv j hj)
      (extended_segment_local_cap hj hr hcap ht)).1
  matrixDerivative j hj t _ := by
    simp only [extendedPolynomialMatrix22_before σ a B hj,extendedPolynomialState42_before σ a hj,if_pos hj]
    exact (shiftedPolynomialMatrix_derivative σ (a j) 42 22 (B j) ((j:ℝ)*h) t).hasDerivWithinAt
  referenceDerivative j hj t _ := by
    simp only [extendedPolynomialState42_before σ a hj,if_pos hj]
    exact (shiftedPolynomialState_derivative σ (a j) 42 ((j:ℝ)*h) t).hasDerivWithinAt
  matrixBound j hj t ht := by
    rw [extendedPolynomialMatrix22_before σ a B hj]
    exact (shiftedPolynomialMatrix22_bounds σ hσ (ha j hj) (B j) (hunit j hj) (hB j hj) (hinv j hj)
      (extended_segment_local_cap hj hr hcap ht)).2.1
  inverseBound j hj t ht := by
    rw [extendedPolynomialMatrix22_before σ a B hj]
    exact (shiftedPolynomialMatrix22_bounds σ hσ (ha j hj) (B j) (hunit j hj) (hB j hj) (hinv j hj)
      (extended_segment_local_cap hj hr hcap ht)).2.2
  matrixResidualBound j hj t ht := by
    simp only [if_pos hj]
    exact (shiftedMatrixResidual42_22_bound σ hσ (ha j hj) (B j)
      (extendedGridTime_signed_local_cap σ hσ hj hr hcap ht)).trans (by nlinarith [hB j hj])
  stateResidualBound j hj t ht := by
    simp only [if_pos hj]
    exact shiftedStateResidual42_bound σ hσ (ha j hj)
      (extendedGridTime_signed_local_cap σ hσ hj hr hcap ht)
  referenceMargin j hj t ht := by
    rw [extendedPolynomialState42_before σ a hj]
    exact outerTubeMargin_mono
      (taylorPolynomial42_margin_uniform (ha j hj)
        (extendedGridTime_signed_local_cap σ hσ hj hr hcap ht)) hR
  matrixJumpNonneg j _ := by split_ifs with hj; exact hδM j hj; exact le_rfl
  stateJumpNonneg j _ := by split_ifs with hj; exact hδX j hj; exact le_rfl
  matrixReset j hj := by
    by_cases hn : j+1<N
    · simp only [if_pos hn,extendedPolynomialMatrix22_before σ a B hj,
        extendedPolynomialMatrix22_before σ a B hn,extendedGridTime_before hn]
      have he : (((j+1:ℕ):ℝ)*h)-(j:ℝ)*h=h := by push_cast; ring
      simpa only [shiftedPolynomialMatrix,he,sub_self,referencePolynomialMatrix,mul_zero,
        variationPolynomialMap_zero,flowEnd_one_comp] using hresetM j hn
    · have he : j+1=N := by omega
      have hj' : j=N-1 := by omega
      rw [if_neg hn,he,hj']
      change ‖extendedReference _ N h r (N-1) (extendedGridTime N h r N)-
        extendedReference _ N h r N (extendedGridTime N h r N)‖≤0
      rw [extendedReference_last_reset _ hN,sub_self,norm_zero]
  stateReset j hj := by
    by_cases hn : j+1<N
    · simp only [if_pos hn,extendedPolynomialState42_before σ a hj,
        extendedPolynomialState42_before σ a hn,extendedGridTime_before hn]
      have he : (((j+1:ℕ):ℝ)*h)-(j:ℝ)*h=h := by push_cast; ring
      simpa only [shiftedPolynomialState,he,sub_self,mul_zero,polynomialPath_taylor_zero] using hresetX j hn
    · have he : j+1=N := by omega
      have hj' : j=N-1 := by omega
      rw [if_neg hn,he,hj']
      change ‖extendedReference _ N h r (N-1) (extendedGridTime N h r N)-
        extendedReference _ N h r N (extendedGridTime N h r N)‖≤0
      rw [extendedReference_last_reset _ hN,sub_self,norm_zero]

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Extended polynomial grid audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Complete extended polynomial grid audited: {count} declarations; standard axioms only."
