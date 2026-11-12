import SolitonClassification.Rotating.ExtendedPolynomialGridEndpoints42

/-! Point certificates can be concatenated without expanding numerical leaves.
Both endpoint states and full matrices agree at the seam. Every ordinary
endpoint reset is retained; only the final extended-grid wrapper drops its
last reset by choosing the last polynomial's own extended endpoint. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure PolynomialPointGridBlock (σ h δX δM : ℝ) (N : ℕ) where
  state : ℕ → State
  matrix : ℕ → FlowEnd
  inner : ∀j≤N, state j∈innerTube
  nodeUnit : ∀j≤N, IsUnit (matrix j)
  nodeNorm : ∀j≤N, ‖matrix j‖≤2000
  nodeInverse : ∀j≤N, ‖Ring.inverse (matrix j)‖≤4000
  stateResetNonneg : 0≤δX
  matrixResetNonneg : 0≤δM
  stateReset : ∀j<N,
    ‖polynomialPath (taylorPolynomial (state j) 42) (σ*h)-state (j+1)‖≤δX
  matrixReset : ∀j<N,
    ‖referencePolynomialMatrix σ (state j) 22 (matrix j) h-matrix (j+1)‖≤δM

namespace PolynomialPointGridBlock

def join {α : Type*} (N : ℕ) (a b : ℕ → α) (j : ℕ) : α :=
  if j≤N then a j else b (j-N)

theorem join_left {α : Type*} {N j : ℕ} (a b : ℕ → α) (hj : j≤N) :
    join N a b j=a j := by simp only [join,if_pos hj]

theorem join_right {α : Type*} {N j : ℕ} (a b : ℕ → α)
    (hseam : a N=b 0) (hj : N≤j) : join N a b j=b (j-N) := by
  by_cases he : j=N
  · subst j
    simpa only [join,le_refl,if_true,Nat.sub_self] using hseam
  · simp only [join,if_neg (by omega : ¬j≤N)]

variable {σ h δX δM : ℝ} {N M : ℕ}

def append (A : PolynomialPointGridBlock σ h δX δM N)
    (B : PolynomialPointGridBlock σ h δX δM M)
    (hstate : A.state N=B.state 0) (hmatrix : A.matrix N=B.matrix 0) :
    PolynomialPointGridBlock σ h δX δM (N+M) where
  state := join N A.state B.state
  matrix := join N A.matrix B.matrix
  inner j hj := by
    by_cases hn : j≤N
    · rw [join_left _ _ hn]
      exact A.inner j hn
    · rw [join_right _ _ hstate (by omega)]
      exact B.inner (j-N) (by omega)
  nodeUnit j hj := by
    by_cases hn : j≤N
    · rw [join_left _ _ hn]
      exact A.nodeUnit j hn
    · rw [join_right _ _ hmatrix (by omega)]
      exact B.nodeUnit (j-N) (by omega)
  nodeNorm j hj := by
    by_cases hn : j≤N
    · rw [join_left _ _ hn]
      exact A.nodeNorm j hn
    · rw [join_right _ _ hmatrix (by omega)]
      exact B.nodeNorm (j-N) (by omega)
  nodeInverse j hj := by
    by_cases hn : j≤N
    · rw [join_left _ _ hn]
      exact A.nodeInverse j hn
    · rw [join_right _ _ hmatrix (by omega)]
      exact B.nodeInverse (j-N) (by omega)
  stateResetNonneg := A.stateResetNonneg
  matrixResetNonneg := A.matrixResetNonneg
  stateReset j hj := by
    by_cases hn : j<N
    · rw [join_left _ _ (by omega : j≤N),join_left _ _ (by omega : j+1≤N)]
      exact A.stateReset j hn
    · rw [join_right _ _ hstate (by omega : N≤j),
        join_right _ _ hstate (by omega : N≤j+1)]
      have he : j+1-N=(j-N)+1 := by omega
      rw [he]
      exact B.stateReset (j-N) (by omega)
  matrixReset j hj := by
    by_cases hn : j<N
    · rw [join_left _ _ (by omega : j≤N),join_left _ _ (by omega : j≤N),
        join_left _ _ (by omega : j+1≤N)]
      exact A.matrixReset j hn
    · rw [join_right _ _ hstate (by omega : N≤j),
        join_right _ _ hmatrix (by omega : N≤j),
        join_right _ _ hmatrix (by omega : N≤j+1)]
      have he : j+1-N=(j-N)+1 := by omega
      rw [he]
      exact B.matrixReset (j-N) (by omega)

variable (A : PolynomialPointGridBlock σ h δX δM N)
    (B : PolynomialPointGridBlock σ h δX δM M)
    (hstate : A.state N=B.state 0) (hmatrix : A.matrix N=B.matrix 0)

theorem append_state_left {j : ℕ} (hj : j≤N) :
    (append A B hstate hmatrix).state j=A.state j := join_left _ _ hj

theorem append_matrix_left {j : ℕ} (hj : j≤N) :
    (append A B hstate hmatrix).matrix j=A.matrix j := join_left _ _ hj

theorem append_state_right {j : ℕ} (hj : N≤j) :
    (append A B hstate hmatrix).state j=B.state (j-N) := join_right _ _ hstate hj

theorem append_matrix_right {j : ℕ} (hj : N≤j) :
    (append A B hstate hmatrix).matrix j=B.matrix (j-N) := join_right _ _ hmatrix hj

theorem append_state_zero : (append A B hstate hmatrix).state 0=A.state 0 :=
  append_state_left A B hstate hmatrix (Nat.zero_le _)

theorem append_matrix_zero : (append A B hstate hmatrix).matrix 0=A.matrix 0 :=
  append_matrix_left A B hstate hmatrix (Nat.zero_le _)

theorem append_state_last : (append A B hstate hmatrix).state (N+M)=B.state M := by
  simpa only [Nat.add_sub_cancel_left] using
    append_state_right A B hstate hmatrix (j:=N+M) (by omega)

theorem append_matrix_last : (append A B hstate hmatrix).matrix (N+M)=B.matrix M := by
  simpa only [Nat.add_sub_cancel_left] using
    append_matrix_right A B hstate hmatrix (j:=N+M) (by omega)

end PolynomialPointGridBlock
end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.PolynomialPointGridBlock.append
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Point-grid block append audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Point-grid block append audited: {count} declarations; standard axioms only."
