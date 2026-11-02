import Lemniscate.PeriodicFredholmAlternative

/-! The nonzero spectral gap uses the real parts of the genuine spectrum.
A nonzero eigenvalue supplies nonemptiness when applying real suprema. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleSpectralGap (h h₁ h₂ : C(AddCircle T, ℂ)) : ℝ :=
  -sSup {r : ℝ | ∃ w : ℂ, w ∈ circleSpectrum T h h₁ h₂ ∧ w ≠ 0 ∧ w.re = r}

theorem circle_spectral_gap_bounds (h h₁ h₂ : C(AddCircle T, ℂ)) (a b : ℝ)
    (hupper : ∀ w : ℂ, w ∈ circleSpectrum T h h₁ h₂ → w ≠ 0 → w.re ≤ -a)
    (w : ℂ) (hw : w ∈ circleSpectrum T h h₁ h₂) (hwne : w ≠ 0) (hlower : -b ≤ w.re) :
    a ≤ circleSpectralGap T h h₁ h₂ ∧ circleSpectralGap T h h₁ h₂ ≤ b := by
  let A : Set ℝ := {r | ∃ z : ℂ, z ∈ circleSpectrum T h h₁ h₂ ∧ z ≠ 0 ∧ z.re = r}
  have hne : A.Nonempty := ⟨w.re,w,hw,hwne,rfl⟩
  have hbd : BddAbove A := ⟨-a,by
    rintro r ⟨z,hz,hzne,rfl⟩
    exact hupper z hz hzne⟩
  have hsup : sSup A ≤ -a := csSup_le hne (by
    rintro r ⟨z,hz,hzne,rfl⟩
    exact hupper z hz hzne)
  have hinf : -b ≤ sSup A := le_trans hlower (le_csSup hbd ⟨w,hw,hwne,rfl⟩)
  constructor
  · change a ≤ -sSup A
    simpa only [neg_neg] using neg_le_neg hsup
  · change -sSup A ≤ b
    simpa only [neg_neg] using neg_le_neg hinf

end Lemniscate
