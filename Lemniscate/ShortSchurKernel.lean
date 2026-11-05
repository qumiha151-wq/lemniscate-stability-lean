import Lemniscate.ShortSchurSymmetry
import Mathlib.Data.Matrix.Basic

/-! All Fourier entries of the seven-mode finite-rank comparison.
Indices here are half-frequencies: n denotes the genuine Fourier mode 2n.
The external columns retain the true untruncated coefficient h(|n-m|). -/
namespace Lemniscate
open Matrix Finset

def shortHeadIndex (n : ℤ) : Option (Fin 15) :=
  if hn : -7 ≤ n ∧ n ≤ 7 then some ⟨(n+7).toNat, by omega⟩ else none

theorem short_head_index_frequency (n : ℤ) (i : Fin 15)
    (hi : shortHeadIndex n = some i) : shortHeadFrequency i = 2*n := by
  unfold shortHeadIndex at hi
  split_ifs at hi with hn
  · cases Option.some.inj hi
    dsimp only [shortHeadFrequency]
    omega

noncomputable def shortOutsideHColumn (r : ℝ) (h : ℕ → ℝ) (k : Fin 3)
    (m : ℤ) (i : Fin 15) : ℝ :=
  if k=0 then ∑ a : Fin 15, shortHouseholder h i a *
    ((shortBlochEntry r h 0 (shortHeadFrequency a) (2*m) +
      shortBlochEntry r h 0 (2*m) (shortHeadFrequency a))/2)
  else (∑ a : Fin 15, (
    (shortHouseholder h * shortNeutral h) i a *
      shortBlochEntry r h (k.castLE (by decide : 3≤5)) (shortHeadFrequency a) (2*m) +
    (shortNeutralInv h * shortHouseholder h) a i *
      shortBlochEntry r h (k.castLE (by decide : 3≤5)) (2*m) (shortHeadFrequency a)))/2

noncomputable def shortOutsideGColumn (r : ℝ) (h : ℕ → ℝ) (k : Fin 3)
    (m : ℤ) : Fin 15 → ℝ :=
  shortStableProjection *ᵥ shortOutsideHColumn r h k m +
    if hk : k.val < 2 then
      shortCenterProjection *ᵥ shortOutsideHColumn r h ⟨k.val+1, by omega⟩ m
    else 0

noncomputable def shortOutsideBernsteinColumn (r : ℝ) (h : ℕ → ℝ)
    (j : Fin 5) (m : ℤ) (i : Fin 15) : ℝ :=
  ∑ k : Fin 3, (shortBernsteinWeight j (k.castLE (by decide : 3≤5)) : ℝ) *
    shortOutsideGColumn r h k m i

noncomputable def shortRawBernsteinEntry (r : ℝ) (h : ℕ → ℝ)
    (j : Fin 5) (n m : ℤ) : ℝ :=
  (if n=m then (1/2:ℝ) else 0) +
    ∑ k : Fin 5, (shortBernsteinWeight j k : ℝ) *
      ((shortBlochEntry r h k (2*n) (2*m) + shortBlochEntry r h k (2*m) (2*n))/2)

noncomputable def shortBernsteinKernel (r : ℝ) (h : ℕ → ℝ)
    (j : Fin 5) (n m : ℤ) : ℝ :=
  match shortHeadIndex n, shortHeadIndex m with
  | some i, some k => shortBernsteinHead r h j i k
  | some i, none => shortOutsideBernsteinColumn r h j m i
  | none, some i => shortOutsideBernsteinColumn r h j n i
  | none, none => shortRawBernsteinEntry r h j n m

theorem short_bernstein_kernel_symmetric (r : ℝ) (h : ℕ → ℝ)
    (j : Fin 5) (n m : ℤ) : shortBernsteinKernel r h j n m = shortBernsteinKernel r h j m n := by
  have hb : (shortBernsteinHead r h j)ᵀ = shortBernsteinHead r h j := by
    simp only [shortBernsteinHead, Matrix.transpose_sum, Matrix.transpose_smul,
      short_g_coefficient_transpose]
  unfold shortBernsteinKernel
  cases hn : shortHeadIndex n <;> cases hm : shortHeadIndex m
  · simp only [shortRawBernsteinEntry, eq_comm, add_comm]
  · rfl
  · rfl
  · rename_i i k
    exact congrFun (congrFun hb k) i

end Lemniscate
