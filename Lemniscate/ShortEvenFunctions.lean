import Lemniscate.ShortCircleCoordinates
import Lemniscate.ShortSobolevNorm

namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0<T)]

def shortEvenDomain : Submodule ℂ (circleH4Domain T) where
  carrier := {f | ∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n=0}
  zero_mem' := by
    intro n _
    change fourierCoeff (0:CircleL2 T) n=0
    rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply,inner_zero_right]
  add_mem' := by
    intro f g hf hg n hn
    simp only [Submodule.coe_add,circle_fourierCoeff_add,hf n hn,hg n hn,add_zero]
  smul_mem' := by
    intro c f hf n hn
    simp only [Submodule.coe_smul_of_tower,circle_fourierCoeff_smul,hf n hn,mul_zero]

theorem short_head_mem_even (v : Fin 15 → ℂ) : circleShortHead T v ∈ shortEvenDomain T := by
  intro n hn
  rw [circle_short_head_fourier]
  have hne (i : Fin 15) : n≠shortHeadFrequency i := by
    rcases hn with ⟨k,hk⟩
    dsimp only [shortHeadFrequency]
    omega
  simp only [if_neg (hne _),mul_zero,Finset.sum_const_zero]

theorem short_neutral_vectors_mem_even :
    circleShortRotationApproximation T ∈ shortEvenDomain T ∧
    circleShortAdjointApproximation T ∈ shortEvenDomain T ∧
    circleHouseholderAnchorH4 T ∈ shortEvenDomain T := by
  rw [circle_short_rotation_head,circle_short_adjoint_head,circle_short_anchor_head]
  exact ⟨short_head_mem_even T _,short_head_mem_even T _,short_head_mem_even T _⟩

theorem short_even_h1_le_v (f : circleH4Domain T) (hf : f ∈ shortEvenDomain T) :
    shortH1Norm T f ≤ shortVNorm T f := by
  have hs : Summable (fun n : ℤ => (1+(n:ℝ)^2)*‖fourierCoeff (f:CircleL2 T) n‖^2) := by
    simpa only [add_mul,one_mul] using
      (circle_fourier_square_summable T (f:CircleL2 T)).add (short_fourier_second_summable T f)
  have hpoint (n : ℤ) : (1+(n:ℝ)^2)*‖fourierCoeff (f:CircleL2 T) n‖^2 ≤
      max (1:ℝ) ((n:ℝ)^4)*‖fourierCoeff (f:CircleL2 T) n‖^2 := by
    by_cases hn : n=0
    · subst n
      norm_num
    by_cases ho : Odd n
    · rw [hf n ho,norm_zero]
      norm_num
    have h1 : n≠1 := by rintro rfl; exact ho (by decide)
    have hm1 : n≠ -1 := by rintro rfl; exact ho (by decide)
    have hcases : n≤ -2 ∨ 2≤n := by omega
    have hsq : (4:ℝ)≤(n:ℝ)^2 := by
      rcases hcases with h | h
      · have hc : (n:ℝ)≤ -2 := by exact_mod_cast h
        nlinarith
      · have hc : (2:ℝ)≤(n:ℝ) := by exact_mod_cast h
        nlinarith
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply le_trans _ (le_max_right _ _)
    nlinarith [mul_nonneg (sq_nonneg (n:ℝ)) (sub_nonneg.mpr hsq)]
  have hsum := hs.tsum_le_tsum hpoint (short_v_weight_summable T f)
  rw [← short_h1_norm_sq_fourier,← short_v_norm_sq_fourier] at hsum
  exact (sq_le_sq₀ (short_h1_norm_nonneg T f) (short_v_norm_nonneg T f)).mp hsum

end Lemniscate
