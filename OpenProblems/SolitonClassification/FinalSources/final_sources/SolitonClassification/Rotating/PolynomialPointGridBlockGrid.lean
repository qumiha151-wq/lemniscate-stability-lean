module

public import SolitonClassification.Rotating.PolynomialPointGridBlock

@[expose] public section

/-! A block assembled from actual point certificates produces the complete
extended reference grid. Internal reset sums are explicit, and the original
nominal endpoint comparison still charges the last ordinary reset. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset UniversalMajorant
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace PolynomialPointGridBlock
variable {σ h δX δM : ℝ} {N : ℕ}
variable (A : PolynomialPointGridBlock σ h δX δM N)

def toExtendedGrid (hσ : |σ|≤1) (hN : 0<N) (r R : ℝ)
    (hh : 0≤h) (hr : 0≤r) (hcap : h+2*r≤(universalStepCap:ℝ))
    (hR : 2400*R≤1/100) (hB0 : A.matrix 0=1) :
    FlowBootstrapGridData σ N ((N:ℝ)*h+2*r) 2400 5000 R (4/10^16) (6/10^40) :=
  extendedPolynomialGrid42 σ hσ N hN h r R A.state A.matrix (fun _=>δX) (fun _=>δM)
    hh hr hcap hR (fun j hj=>A.inner j (by omega)) hB0
    (fun j hj=>A.nodeUnit j (by omega)) (fun j hj=>A.nodeNorm j (by omega))
    (fun j hj=>A.nodeInverse j (by omega))
    (fun _ _=>A.stateResetNonneg) (fun _ _=>A.matrixResetNonneg)
    (fun j hj=>A.stateReset j (by omega)) (fun j hj=>A.matrixReset j (by omega))

variable (hσ : |σ|≤1) (hN : 0<N) (r R : ℝ)
    (hh : 0≤h) (hr : 0≤r) (hcap : h+2*r≤(universalStepCap:ℝ))
    (hR : 2400*R≤1/100) (hB0 : A.matrix 0=1)

local notation "G" => A.toExtendedGrid hσ hN r R hh hr hcap hR hB0

theorem extended_initial_reference : (G).reference 0 0=A.state 0 := by
  change extendedPolynomialState42 σ A.state N h r 0 0=A.state 0
  rw [extendedPolynomialState42_before σ A.state hN]
  simpa only [Nat.cast_zero,zero_mul] using
    shiftedPolynomialState_zero σ (A.state 0) 42 0

theorem extended_state_jump_sum :
    (∑j∈range N,(G).stateJump j)=((N-1:ℕ):ℝ)*δX := by
  change (∑j∈range N,if j+1<N then δX else 0)=_
  rw [internal_reset_sum hN]
  simp

theorem extended_matrix_jump_sum :
    (∑j∈range N,(G).matrixJump j)=((N-1:ℕ):ℝ)*δM := by
  change (∑j∈range N,if j+1<N then δM else 0)=_
  rw [internal_reset_sum hN]
  simp

theorem extended_state_jump_sum_le :
    (∑j∈range N,(G).stateJump j)≤(N:ℝ)*δX := by
  rw [extended_state_jump_sum]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N 1) A.stateResetNonneg

theorem extended_matrix_jump_sum_le :
    (∑j∈range N,(G).matrixJump j)≤(N:ℝ)*δM := by
  rw [extended_matrix_jump_sum]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N 1) A.matrixResetNonneg

theorem extended_last_state_jump : (G).stateJump (N-1)=0 := by
  change (if N-1+1<N then δX else 0)=0
  rw [Nat.sub_add_cancel hN,if_neg (lt_irrefl N)]

theorem extended_last_matrix_jump : (G).matrixJump (N-1)=0 := by
  change (if N-1+1<N then δM else 0)=0
  rw [Nat.sub_add_cancel hN,if_neg (lt_irrefl N)]

theorem nominal_in_last_segment : (N:ℝ)*h∈Icc ((G).time (N-1)) ((G).time N) :=
  center_endpoint_in_extended_last_segment hN hh hr

theorem nominal_state_comparison {x : State} {E : ℝ}
    (hx : ‖x-(G).reference (N-1) ((N:ℝ)*h)‖≤E) :
    ‖x-A.state N‖≤E+δX := by
  apply extendedPolynomialState42_center_comparison σ A.state hN h r hx
  simpa only [Nat.sub_add_cancel hN] using A.stateReset (N-1) (by omega)

theorem nominal_matrix_comparison {P : FlowEnd} {E : ℝ}
    (hP : ‖P-(G).matrix (N-1) ((N:ℝ)*h)‖≤E) :
    ‖P-A.matrix N‖≤E+δM := by
  apply extendedPolynomialMatrix22_center_comparison σ A.state A.matrix hN h r hP
  simpa only [Nat.sub_add_cancel hN] using A.matrixReset (N-1) (by omega)

end PolynomialPointGridBlock
end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.PolynomialPointGridBlock.toExtendedGrid
#print axioms SolitonClassification.Rotating.PolynomialPointGridBlock.nominal_matrix_comparison
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Point-grid extended assembly audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Point-grid extended assembly audited: {count} declarations; standard axioms only."
