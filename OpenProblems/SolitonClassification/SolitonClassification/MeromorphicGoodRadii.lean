import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
namespace ClosedSimilarity.MeromorphicGrowth

/-- For a locally bounded monotone size function there are arbitrarily
large radii across which a reciprocal-size increment costs at most a doubling. -/
theorem exists_doubling_radius (H : ℝ → ℝ) (pos : ∀r,0<H r) (mono : Monotone H)
    (R : ℝ) : ∃r, R≤r ∧ H (r+4/H r)≤2*H r := by
  by_contra! bad
  let x : ℕ → ℝ := Nat.rec R (fun _ t=>t+4/H t)
  have step (n : ℕ) : x (n+1)=x n+4/H (x n) := rfl
  have lo (n : ℕ) : R≤x n := by
    induction n with
    | zero => exact le_rfl
    | succ n ih => rw [step]; exact ih.trans (le_add_of_nonneg_right (by positivity [pos (x n)]))
  have grow (n : ℕ) : 2*H (x n)<H (x (n+1)) := by simpa only [step] using bad (x n) (lo n)
  have budget (n : ℕ) : x n+8/H (x n)≤R+8/H R := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      apply le_trans _ ih
      have drop : 8/H (x (n+1))≤4/H (x n) := by
        rw [div_le_div_iff₀ (pos _) (pos _)]
        linarith only [grow n]
      calc x (n+1)+8/H (x (n+1)) ≤ x (n+1)+4/H (x n) := add_le_add_right drop _
           _ = x n+8/H (x n) := by rw [step n]; ring
  have lower (n : ℕ) : ((n:ℝ)+1)*H R≤H (x n) := by
    induction n with
    | zero => simp [x]
    | succ n ih =>
      have init := mono (lo n)
      push_cast
      linarith only [grow n,ih,init]
  obtain ⟨n,hn⟩ := exists_nat_gt (H (R+8/H R)/H R)
  have above := (div_lt_iff₀ (pos R)).mp hn
  have ub : x n≤R+8/H R := (le_add_of_nonneg_right (by positivity [pos (x n)])).trans (budget n)
  linarith only [above,lower n,mono ub,pos R]

end ClosedSimilarity.MeromorphicGrowth

