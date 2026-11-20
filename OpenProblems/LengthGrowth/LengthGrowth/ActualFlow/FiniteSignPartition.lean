import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.FiniteSign

/-- Ordered weakly one-sign pieces. Tangential zeros, including intervals of
zeros in a piece, require no extra pieces. -/
inductive Pieces (k : ℝ → ℝ) : Nat → ℝ → ℝ → Prop
  | empty (a : ℝ) : Pieces k 0 a a
  | append {n : Nat} {a b d : ℝ} (prev : Pieces k n a b) (hbd : b≤d)
      (sign : (∀s∈Icc b d, 0≤k s) ∨ (∀s∈Icc b d, k s≤0)) : Pieces k (n+1) a d

theorem Pieces.ordered {k : ℝ→ℝ} {n : Nat} {a b : ℝ} (part : Pieces k n a b) : a≤b := by
  induction part with
  | empty => exact le_rfl
  | append _ h _ ih => exact ih.trans h

theorem Pieces.cubic_upper {k v F : ℝ→ℝ} {n : Nat} {a b H : ℝ}
    (part : Pieces k n a b) (hk : Continuous k) (hF : Continuous F)
    (hd : ∀s, HasDerivAt v (F s-k s^3/2) s)
    (hv : ∀s∈Icc a b, |v s|≤H) :
    (∫ s in a..b, |k s|^3) ≤ 2*(∫s in a..b, |F s|)+4*n*H := by
  induction part with
  | empty => simp
  | @append n a b d prev hbd hsign ih =>
    have hab:=prev.ordered
    have hv' : ∀s∈Icc a b, |v s|≤H := fun s hs=>hv s ⟨hs.1,hs.2.trans hbd⟩
    have hvb:=abs_le.mp (hv b ⟨hab,hbd⟩)
    have hvd:=abs_le.mp (hv d ⟨hab.trans hbd,le_rfl⟩)
    have iF : IntervalIntegrable F volume b d := hF.intervalIntegrable _ _
    have ik : Continuous (fun s=>k s^3/2) := (hk.pow _).div_const _
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a:=b) (b:=d) (fun s _=>hd s) ((hF.sub ik).intervalIntegrable _ _)
    rw [intervalIntegral.integral_sub iF (ik.intervalIntegrable _ _),
      intervalIntegral.integral_div] at hFTC
    have hpart : (∫s in b..d,|k s|^3) ≤ 2*(∫s in b..d,|F s|)+4*H := by
      rcases hsign with hp|hn
      · have hEq : (∫s in b..d,|k s|^3)=(∫s in b..d,k s^3) := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le hbd]
          intro x hx; change |k x|^3=k x^3; rw [abs_of_nonneg (hp x hx)]
        have hle:=intervalIntegral.integral_mono_on hbd iF (hF.abs.intervalIntegrable _ _)
          (fun s _ => le_abs_self (F s))
        rw [hEq];linarith
      · have hEq : (∫s in b..d,|k s|^3)= -(∫s in b..d,k s^3) := by
          rw [← intervalIntegral.integral_neg]
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le hbd]
          intro x hx; change |k x|^3= -(k x^3); rw [abs_of_nonpos (hn x hx)]; ring
        have hle:=intervalIntegral.integral_mono_on (μ:=volume) hbd (hF.neg.intervalIntegrable _ _)
          (hF.abs.intervalIntegrable _ _) (fun s _ => neg_le_abs (F s))
        change (∫s in b..d,-F s)≤_ at hle
        rw [intervalIntegral.integral_neg] at hle
        rw [hEq];linarith
    rw [←intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (f:=fun s=>|k s|^3) ((hk.abs.pow 3).intervalIntegrable a b)
      ((hk.abs.pow 3).intervalIntegrable b d),
      ←intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (f:=fun s=>|F s|) (hF.abs.intervalIntegrable a b)
        (hF.abs.intervalIntegrable b d)]
    push_cast
    nlinarith only [ih hv',hpart]

end LengthGrowth.FiniteSign
#print axioms LengthGrowth.FiniteSign.Pieces.cubic_upper
