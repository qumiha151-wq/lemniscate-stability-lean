module

public import SolitonClassification.Rotating.ExtendedPolynomialGridAssembly42

@[expose] public section

/-! Distinguish the original center endpoint from the extended terminal node.
The original point a_N/B_N is used only in explicitly charged center
comparisons. It is not the new terminal reference or a terminal reset. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset UniversalMajorant
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem extendedPolynomialState42_terminal (σ : ℝ) (a : ℕ → State)
    {N : ℕ} (hN : 0<N) (h r : ℝ) :
    extendedPolynomialState42 σ a N h r N=
      fun _ => polynomialPath (taylorPolynomial (a (N-1)) 42) (σ*(h+2*r)) := by
  rw [extendedPolynomialState42,extendedReference_terminal]
  funext t
  dsimp only [shiftedPolynomialState]
  rw [extended_last_local_time hN]

theorem extendedPolynomialMatrix22_terminal (σ : ℝ) (a : ℕ → State) (B : ℕ → FlowEnd)
    {N : ℕ} (hN : 0<N) (h r : ℝ) :
    extendedPolynomialMatrix22 σ a B N h r N=
      fun _ => referencePolynomialMatrix σ (a (N-1)) 22 (B (N-1)) (h+2*r) := by
  rw [extendedPolynomialMatrix22,extendedReference_terminal]
  funext t
  dsimp only [shiftedPolynomialMatrix]
  rw [extended_last_local_time hN]

theorem original_center_local_time {N : ℕ} (hN : 0<N) (h : ℝ) :
    (N:ℝ)*h-((N-1:ℕ):ℝ)*h=h := by
  simpa only [mul_zero,add_zero] using extended_last_local_time hN h 0

theorem extendedPolynomialState42_center (σ : ℝ) (a : ℕ → State)
    {N : ℕ} (hN : 0<N) (h r : ℝ) :
    extendedPolynomialState42 σ a N h r (N-1) ((N:ℝ)*h)=
      polynomialPath (taylorPolynomial (a (N-1)) 42) (σ*h) := by
  rw [extendedPolynomialState42_before σ a (by omega : N-1<N)]
  dsimp only [shiftedPolynomialState]
  rw [original_center_local_time hN]

theorem extendedPolynomialMatrix22_center (σ : ℝ) (a : ℕ → State) (B : ℕ → FlowEnd)
    {N : ℕ} (hN : 0<N) (h r : ℝ) :
    extendedPolynomialMatrix22 σ a B N h r (N-1) ((N:ℝ)*h)=
      referencePolynomialMatrix σ (a (N-1)) 22 (B (N-1)) h := by
  rw [extendedPolynomialMatrix22_before σ a B (by omega : N-1<N)]
  dsimp only [shiftedPolynomialMatrix]
  rw [original_center_local_time hN]

theorem extendedPolynomialState42_center_comparison (σ : ℝ) (a : ℕ → State)
    {N : ℕ} (hN : 0<N) (h r : ℝ) {x : State} {E δ : ℝ}
    (hx : ‖x-extendedPolynomialState42 σ a N h r (N-1) ((N:ℝ)*h)‖≤E)
    (hc : ‖polynomialPath (taylorPolynomial (a (N-1)) 42) (σ*h)-a N‖≤δ) :
    ‖x-a N‖≤E+δ := by
  rw [extendedPolynomialState42_center σ a hN] at hx
  have ht := dist_triangle x (polynomialPath (taylorPolynomial (a (N-1)) 42) (σ*h)) (a N)
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add hx hc)

theorem extendedPolynomialMatrix22_center_comparison (σ : ℝ) (a : ℕ → State) (B : ℕ → FlowEnd)
    {N : ℕ} (hN : 0<N) (h r : ℝ) {P : FlowEnd} {E δ : ℝ}
    (hP : ‖P-extendedPolynomialMatrix22 σ a B N h r (N-1) ((N:ℝ)*h)‖≤E)
    (hc : ‖referencePolynomialMatrix σ (a (N-1)) 22 (B (N-1)) h-B N‖≤δ) :
    ‖P-B N‖≤E+δ := by
  rw [extendedPolynomialMatrix22_center σ a B hN] at hP
  have ht := dist_triangle P (referencePolynomialMatrix σ (a (N-1)) 22 (B (N-1)) h) (B N)
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add hP hc)

theorem internal_reset_sum {N : ℕ} (hN : 0<N) (δ : ℕ → ℝ) :
    (∑j∈range N,if j+1<N then δ j else 0)=∑j∈range (N-1),δ j := by
  have he : N-1+1=N := Nat.sub_add_cancel hN
  calc
    _ = (∑j∈range (N-1),if j+1<N then δ j else 0)+
      (if (N-1)+1<N then δ (N-1) else 0) := by
      conv_lhs => rw [←he]
      rw [sum_range_succ]
      simp only [he]
    _ = _ := by
      rw [he,if_neg (lt_irrefl N),add_zero]
      apply sum_congr rfl
      intro j hj
      rw [if_pos (by have := mem_range.mp hj; omega : j+1<N)]

section ConstructorEndpoints
variable (σ : ℝ) (hσ : |σ|≤1) (N : ℕ) (hN : 0<N) (h r R : ℝ)
  (a : ℕ → State) (B : ℕ → FlowEnd) (δX δM : ℕ → ℝ)
  (hh : 0≤h) (hr : 0≤r) (hcap : h+2*r≤(universalStepCap:ℝ)) (hR : 2400*R≤1/100)
  (ha : ∀j<N,a j∈innerTube) (hB0 : B 0=1)
  (hunit : ∀j<N,IsUnit (B j)) (hB : ∀j<N,‖B j‖≤2000)
  (hinv : ∀j<N,‖Ring.inverse (B j)‖≤4000)
  (hδX : ∀j,j+1<N→0≤δX j) (hδM : ∀j,j+1<N→0≤δM j)
  (hresetX : ∀j,j+1<N→‖polynomialPath (taylorPolynomial (a j) 42) (σ*h)-a (j+1)‖≤δX j)
  (hresetM : ∀j,j+1<N→‖referencePolynomialMatrix σ (a j) 22 (B j) h-B (j+1)‖≤δM j)

local notation "G" => extendedPolynomialGrid42 σ hσ N hN h r R a B δX δM hh hr hcap hR
  ha hB0 hunit hB hinv hδX hδM hresetX hresetM

theorem extendedGrid42_initial_reference : (G).reference 0 0=a 0 := by
  change extendedPolynomialState42 σ a N h r 0 0=a 0
  rw [extendedPolynomialState42_before σ a hN]
  simpa only [Nat.cast_zero,zero_mul] using shiftedPolynomialState_zero σ (a 0) 42 0

theorem extendedGrid42_last_stateJump : (G).stateJump (N-1)=0 := by
  change (if N-1+1<N then δX (N-1) else 0)=0
  simp only [Nat.sub_add_cancel hN,lt_self_iff_false,if_false]

theorem extendedGrid42_last_matrixJump : (G).matrixJump (N-1)=0 := by
  change (if N-1+1<N then δM (N-1) else 0)=0
  simp only [Nat.sub_add_cancel hN,lt_self_iff_false,if_false]

theorem extendedGrid42_stateJump_sum : (∑j∈range N,(G).stateJump j)=∑j∈range (N-1),δX j :=
  internal_reset_sum hN δX

theorem extendedGrid42_matrixJump_sum : (∑j∈range N,(G).matrixJump j)=∑j∈range (N-1),δM j :=
  internal_reset_sum hN δM

theorem extendedGrid42_center_in_last_segment :
    (N:ℝ)*h∈Icc ((G).time (N-1)) ((G).time N) :=
  center_endpoint_in_extended_last_segment hN hh hr

end ConstructorEndpoints

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Extended polynomial endpoints audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Extended versus center endpoints audited: {count} declarations; standard axioms only."

end
