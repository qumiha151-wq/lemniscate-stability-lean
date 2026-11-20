import LengthGrowth.ActualFlow.FiniteSignPartition

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ActualFlow.CriticalDensity

/-- Each interval omits one of the two strict excursions beyond ±δ.
Arbitrarily many smaller changes of sign are allowed. -/
inductive Pieces (k : ℝ → ℝ) (δ : ℝ) : ℕ → ℝ → ℝ → Prop
  | empty (a : ℝ) : Pieces k δ 0 a a
  | append {n : ℕ} {a b d : ℝ} (prev : Pieces k δ n a b) (hbd : b ≤ d)
      (sign : (∀ s ∈ Icc b d, -δ ≤ k s) ∨ (∀ s ∈ Icc b d, k s ≤ δ)) :
      Pieces k δ (n+1) a d

theorem Pieces.ordered {k : ℝ → ℝ} {δ : ℝ} {n : ℕ} {a b : ℝ}
    (p : Pieces k δ n a b) : a ≤ b := by
  induction p with
  | empty => exact le_rfl
  | append _ h _ ih => exact ih.trans h

/-- Measured on every subarc of one RMS-normalized period to allow
arbitrary basepoints of the stress window. -/
def Count (k : ℝ → ℝ) (P : ℝ) (N : ℕ) : Prop :=
  ∀ a b : ℝ, a ≤ b → b ≤ a+P → ∃ n ≤ N+1, Pieces k (1/2) n a b

theorem pieces_of_weak_sign {k : ℝ → ℝ} {n : ℕ} {a b δ : ℝ}
    (p : LengthGrowth.FiniteSign.Pieces k n a b) (hδ : 0 ≤ δ) : Pieces k δ n a b := by
  induction p with
  | empty => exact .empty _
  | append _ h ss ih =>
    apply Pieces.append ih h
    rcases ss with hp|hn
    · exact Or.inl (fun x hx => (neg_nonpos.mpr hδ).trans (hp x hx))
    · exact Or.inr (fun x hx => (hn x hx).trans hδ)

end LengthGrowth.ActualFlow.CriticalDensity
