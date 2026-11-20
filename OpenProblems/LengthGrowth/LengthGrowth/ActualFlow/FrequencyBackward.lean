import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

/-! Scalar comparison for the Rayleigh frequency in a backward uniqueness argument. -/
noncomputable section
open Set
namespace LengthGrowth.FrequencyBackward

private theorem frequency_bound {S u a : ℝ} {Q : ℝ → ℝ} (su : S ≤ u)
    (cont : ContinuousOn Q (Icc S u))
    (rate : ∀ x ∈ Ioo S u, DifferentiableAt ℝ Q x ∧ deriv Q x ≤ a * Q x) :
    Q u ≤ Q S * Real.exp (a * (u - S)) := by
  let w := fun x : ℝ => Real.exp (a * (u - x))
  have dw (x : ℝ) : HasDerivAt w (w x * (-a)) x := by
    simpa [w] using (((hasDerivAt_const x u).sub (hasDerivAt_id x)).const_mul a).exp
  have df (x : ℝ) (hx : x ∈ Ioo S u) :
      HasDerivAt (fun y => Q y * w y) (deriv Q x * w x + Q x * (w x * (-a))) x :=
    (rate x hx).1.hasDerivAt.mul (dw x)
  have mono : AntitoneOn (fun x => Q x * w x) (Icc S u) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (cont.mul (fun x _ => (dw x).continuousAt.continuousWithinAt))
    · rw [interior_Icc]
      exact fun x hx => (df x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      change deriv (fun y => Q y * w y) x ≤ 0
      rw [(df x hx).deriv]
      have weight : 0 ≤ w x := (Real.exp_pos _).le
      nlinarith only [mul_le_mul_of_nonneg_right (rate x hx).2 weight]
  have bound := mono (show S ∈ Icc S u from ⟨le_rfl,su⟩)
    (show u ∈ Icc S u from ⟨su,le_rfl⟩) su
  simpa [w] using bound

/-- On a putative first-zero interval the squared norm has an explicit positive
lower bound at the endpoint. The frequency is only defined analytically before
that endpoint: no continuity there, or bound on its terminal value, is needed. -/
theorem first_zero_lower_bound {S T a b c : ℝ} {Z Q : ℝ → ℝ} (st : S < T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (qS : 0 ≤ Q S)
    (zpos : ∀ x ∈ Ico S T, 0 < Z x)
    (qcont : ContinuousOn Q (Ico S T)) (zcont : ContinuousOn Z (Icc S T))
    (qrate : ∀ x ∈ Ioo S T, DifferentiableAt ℝ Q x ∧ deriv Q x ≤ a * Q x)
    (zrate : ∀ x ∈ Ioo S T, DifferentiableAt ℝ Z x ∧
      -(b * Q x + c * Real.sqrt (Q x)) * Z x ≤ deriv Z x) :
    let M := Q S * Real.exp (a * (T - S))
    Z S * Real.exp ((b * M + c * Real.sqrt M) * (S - T)) ≤ Z T := by
  let M := Q S * Real.exp (a * (T - S))
  let K := b * M + c * Real.sqrt M
  let w := fun x : ℝ => Real.exp (K * (x - T))
  have bound (x : ℝ) (hx : x ∈ Ioo S T) : Q x ≤ M := by
    apply (frequency_bound hx.1.le
      (qcont.mono (fun _ hy => ⟨hy.1,hy.2.trans_lt hx.2⟩))
      (fun y hy => qrate y ⟨hy.1,hy.2.trans hx.2⟩)).trans
    apply mul_le_mul_of_nonneg_left _ qS
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2.le S) ha)
  have dw (x : ℝ) : HasDerivAt w (w x * K) x := by
    simpa [w] using (((hasDerivAt_id x).sub (hasDerivAt_const x T)).const_mul K).exp
  have df (x : ℝ) (hx : x ∈ Ioo S T) :
      HasDerivAt (fun y => Z y * w y) (deriv Z x * w x + Z x * (w x * K)) x :=
    (zrate x hx).1.hasDerivAt.mul (dw x)
  have mono : MonotoneOn (fun x => Z x * w x) (Icc S T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (zcont.mul (fun x _ => (dw x).continuousAt.continuousWithinAt))
    · rw [interior_Icc]
      exact fun x hx => (df x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      change 0 ≤ deriv (fun y => Z y * w y) x
      rw [(df x hx).deriv]
      have cap : b * Q x + c * Real.sqrt (Q x) ≤ K :=
        add_le_add (mul_le_mul_of_nonneg_left (bound x hx) hb)
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (bound x hx)) hc)
      have normRate := (mul_le_mul_of_nonneg_right (neg_le_neg cap) (zpos x ⟨hx.1.le,hx.2⟩).le).trans
        (zrate x hx).2
      have weight : 0 ≤ w x := (Real.exp_pos _).le
      nlinarith only [mul_le_mul_of_nonneg_right normRate weight]
  have both := mono (show S ∈ Icc S T from ⟨le_rfl,st.le⟩)
    (show T ∈ Icc S T from ⟨st.le,le_rfl⟩) st.le
  simpa [w,K,M] using both

/-- Positivity propagates throughout a finite interval if the frequency
inequalities hold whenever the squared norm is positive. -/
theorem positive_at_right {S T a b c : ℝ} {Z Q : ℝ → ℝ} (st : S ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (qS : 0 ≤ Q S) (zS : 0 < Z S)
    (zcont : ContinuousOn Z (Icc S T))
    (qcont : ContinuousOn Q {x ∈ Icc S T | 0 < Z x})
    (rates : ∀ x ∈ Ioo S T, 0 < Z x →
      (DifferentiableAt ℝ Q x ∧ deriv Q x ≤ a * Q x) ∧
      (DifferentiableAt ℝ Z x ∧ -(b * Q x + c * Real.sqrt (Q x)) * Z x ≤ deriv Z x)) :
    0 < Z T := by
  by_contra! terminal
  let zeros := {x ∈ Icc S T | Z x ≤ 0}
  have compact : IsCompact zeros := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.isClosed_le zcont continuousOn_const) (fun _ hx => hx.1)
  obtain ⟨u,hu,first⟩ := compact.exists_isMinOn
    (show zeros.Nonempty from ⟨T,⟨st,le_rfl⟩,terminal⟩) continuous_id.continuousOn
  have su : S < u := lt_of_le_of_ne hu.1.1 (by rintro rfl; exact (not_le.mpr zS) hu.2)
  have pos (x : ℝ) (hx : x ∈ Ico S u) : 0 < Z x := by
    by_contra! nonpos
    exact (not_le.mpr hx.2) (first (show x ∈ zeros from ⟨⟨hx.1,hx.2.le.trans hu.1.2⟩,nonpos⟩))
  have sub (x : ℝ) (hx : x ∈ Ioo S u) : x ∈ Ioo S T := ⟨hx.1,hx.2.trans_le hu.1.2⟩
  have lower := first_zero_lower_bound su ha hb hc qS pos
    (qcont.mono (fun x hx => ⟨⟨hx.1,hx.2.le.trans hu.1.2⟩,pos x hx⟩))
    (zcont.mono (fun _ hx => ⟨hx.1,hx.2.trans hu.1.2⟩))
    (fun x hx => (rates x (sub x hx) (pos x ⟨hx.1.le,hx.2⟩)).1)
    (fun x hx => (rates x (sub x hx) (pos x ⟨hx.1.le,hx.2⟩)).2)
  exact (not_le.mpr ((mul_pos zS (Real.exp_pos _)).trans_le lower)) hu.2

end LengthGrowth.FrequencyBackward
