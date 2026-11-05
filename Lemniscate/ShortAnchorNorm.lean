import Lemniscate.ShortSineSobolevTail
import Lemniscate.PeriodicHouseholderAnchor

/-! The fixed neutral anchor has the same phase as the new sine vectors.
Its two low-order norms follow from the exact finite sine identities. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

theorem short_anchor_eq_I_sine :
    circleHouseholderAnchorH4 T = I • circleSineH4 T 0 := by
  have hfactor : I*evenSineFactor = evenCosineFactor := by
    simp [evenSineFactor,← mul_assoc]
  simp only [circleSineH4,smul_smul,hfactor]
  rfl

theorem short_anchor_norms :
    shortVNorm T (circleHouseholderAnchorH4 T) = 4 ∧
      shortH1Norm T (circleHouseholderAnchorH4 T)^2 = 5 ∧
      shortH1Norm T (circleHouseholderAnchorH4 T) ≤ (5/2:ℝ) := by
  have heq : circleSineTrialH4 T 1 (fun _ => (1:ℂ)) = circleSineH4 T 0 := by
    simp [circleSineTrialH4,Fin.sum_univ_succ]
  have hn := short_sine_trial_norms_sq T (fun _ : Fin 1 => (1:ℂ))
  rw [heq] at hn
  norm_num [Fin.sum_univ_succ] at hn
  have hV : shortVNorm T (circleSineH4 T 0) = 4 := by
    nlinarith only [hn.2.2,short_v_norm_nonneg T (circleSineH4 T 0)]
  have hH : shortH1Norm T (circleSineH4 T 0) ≤ (5/2:ℝ) := by
    nlinarith only [hn.2.1,short_h1_norm_nonneg T (circleSineH4 T 0)]
  rw [short_anchor_eq_I_sine,short_v_norm_smul,short_h1_norm_smul,
    Complex.norm_I,one_mul,one_mul]
  exact ⟨hV,hn.2.1,hH⟩

end Lemniscate
