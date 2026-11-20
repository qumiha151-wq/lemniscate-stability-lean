import SolitonClassification.FrozenStress
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Finite-interval barriers for the corrected transverse stress. -/
noncomputable section
open Set
namespace ClosedSimilarity.FrozenStress

private theorem one_sided_tail {S T B c d : ℝ} {h J A : ℝ → ℝ} (st : S ≤ T)
    (bc : 0 ≤ B) (cc : 0 < c) (hc : ContinuousOn h (Icc S T))
    (jc : ContinuousOn J (Icc S T)) (pos : ∀ x ∈ Icc S T, 0 < h x-d)
    (rate : ∀ x ∈ Ioo S T, DifferentiableAt ℝ h x ∧ DifferentiableAt ℝ J x ∧
      c ≤ deriv h x ∧ deriv J x ≤ B/(A x)^2 ∧ h x-d ≤ A x) :
    J T-J S ≤ B/(c*(h S-d)) := by
  let g := fun x => J x + (B/c)/(h x-d)
  have cnt : ContinuousOn g (Icc S T) := jc.add
    (continuousOn_const.div (hc.sub continuousOn_const) (fun x hx => (pos x hx).ne'))
  have step (x : ℝ) (hx : x ∈ Ioo S T) : HasDerivAt g
      (deriv J x+ (-(B/c)*deriv h x)/(h x-d)^2) x := by
    obtain ⟨hx₁,hx₂,-⟩ := rate x hx
    have pp := pos x ⟨hx.1.le,hx.2.le⟩
    convert! hx₂.hasDerivAt.add ((hasDerivAt_const x (B/c)).div
      (hx₁.hasDerivAt.sub_const d) pp.ne') using 1
    ring
  have desc : AntitoneOn g (Icc S T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) cnt
    · rw [interior_Icc]
      exact fun x hx => (step x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(step x hx).deriv]
      obtain ⟨_,_,speed,error,cap⟩ := rate x hx
      have pp := pos x ⟨hx.1.le,hx.2.le⟩
      have lsq := pow_le_pow_left₀ pp.le cap 2
      have e₁ : deriv J x ≤ B/(h x-d)^2 :=
        error.trans (div_le_div_of_nonneg_left bc (pow_pos pp 2) lsq)
      have e₂ : B ≤ (B/c)*deriv h x := by
        calc B = (B/c)*c := (div_mul_cancel₀ _ cc.ne').symm
             _ ≤ _ := mul_le_mul_of_nonneg_left speed (div_nonneg bc cc.le)
      calc
        _ ≤ B/(h x-d)^2+(-(B/c)*deriv h x)/(h x-d)^2 := add_le_add e₁ le_rfl
        _ = (B-(B/c)*deriv h x)/(h x-d)^2 := by ring
        _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr e₂) (sq_nonneg _)
  have aux := desc (show S∈Icc S T from ⟨le_rfl,st⟩) (show T∈Icc S T from ⟨st,le_rfl⟩) st
  change J T+(B/c)/(h T-d) ≤ J S+(B/c)/(h S-d) at aux
  rw [div_mul_eq_div_div]
  linarith [div_nonneg (div_nonneg bc cc.le) (pos T ⟨st,le_rfl⟩).le]

/-- An explicit drift budget on every interval where the radial speed is
bounded below and the transverse error decays quadratically in the amplitude. -/
theorem corrected_tail {S T B c d : ℝ} {h J A : ℝ → ℝ} (st : S ≤ T)
    (bc : 0 ≤ B) (cc : 0 < c) (hc : ContinuousOn h (Icc S T))
    (jc : ContinuousOn J (Icc S T)) (pos : ∀ x ∈ Icc S T, 0 < h x-d)
    (rate : ∀ x ∈ Ioo S T, DifferentiableAt ℝ h x ∧ DifferentiableAt ℝ J x ∧
      c ≤ deriv h x ∧ |deriv J x| ≤ B/(A x)^2 ∧ h x-d ≤ A x) :
    |J T-J S| ≤ B/(c*(h S-d)) := by
  apply abs_le.mpr
  constructor
  · have lo := one_sided_tail (J:=fun x => -J x) st bc cc hc jc.neg pos
      (fun x hx => by
        obtain ⟨a,b,v,e,cap⟩ := rate x hx
        refine ⟨a,b.neg,v,?_,cap⟩
        change deriv (-J) x ≤ _
        rw [b.hasDerivAt.neg.deriv]
        linarith [(abs_le.mp e).1])
    linarith
  · exact one_sided_tail st bc cc hc jc pos fun x hx => by
      obtain ⟨a,b,v,e,cap⟩ := rate x hx
      exact ⟨a,b,v,(abs_le.mp e).2,cap⟩

theorem negative_tail_margin {J0 J D : ℝ}
    (start : J0 < -0.09) (hD : 10.7 < D)
    (drift : |J-J0| ≤ 0.37/(0.61*D)) : J < -0.033 := by
  have hpos : 0 < 0.61*D := by linarith
  have tiny : (0.37:ℝ)/(0.61*D) < 0.057 := (div_lt_iff₀ hpos).mpr (by linarith)
  linarith [(abs_le.mp drift).2]

theorem positive_tail_margin {J0 J D : ℝ}
    (start : 0.8 < J0) (hD : 10.7 < D)
    (drift : |J-J0| ≤ 0.77/(0.28*D)) : 0.542 < J := by
  have hpos : 0 < 0.28*D := by linarith
  have tiny : (0.77:ℝ)/(0.28*D) < 0.258 := (div_lt_iff₀ hpos).mpr (by linarith)
  linarith [(abs_le.mp drift).1]

end ClosedSimilarity.FrozenStress
