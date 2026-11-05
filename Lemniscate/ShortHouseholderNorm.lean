import Lemniscate.Algebra
import Mathlib.Analysis.InnerProductSpace.Basic

/-! A direct Cauchy--Schwarz proof of the norm bound for a weighted
Householder reflection. No singular-value calculation is needed. -/
namespace Lemniscate
open scoped ComplexConjugate

theorem short_rank_one_involution_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u v : E) (s : ℝ) (hs : 1 < s)
    (hvu : inner ℂ v u = 2)
    (hproduct : s^2*‖u‖^2*‖v‖^2 ≤ (s^2+1)^2) (x : E) :
    ‖x-inner ℂ v x • u‖ ≤ s*‖x‖ := by
  let b := inner ℂ v x
  let y := ((s^2-1:ℝ):ℂ) • x+b • u
  have hs0 : 0 ≤ s := by linarith
  have hs2 : 0 < s^2-1 := by nlinarith only [hs]
  have hv0 : 0 < ‖v‖ := by
    apply norm_pos_iff.mpr
    intro hv
    rw [hv,inner_zero_left] at hvu
    norm_num at hvu
  have hinner : inner ℂ v y = ((s^2+1:ℝ):ℂ)*b := by
    dsimp only [y]
    rw [inner_add_right,inner_smul_right,inner_smul_right,hvu]
    dsimp only [b]
    push_cast
    ring
  have hc := norm_inner_le_norm (𝕜 := ℂ) v y
  rw [hinner,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ s^2+1)] at hc
  have hc2 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (s^2+1)*‖b‖) hc 2
  have hy : ‖y‖^2 = (s^2-1)^2*‖x‖^2+
      2*(s^2-1)*(inner ℂ x (b • u)).re+‖b‖^2*‖u‖^2 := by
    dsimp only [y]
    rw [norm_add_sq (𝕜 := ℂ)]
    simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs2,
      inner_smul_left,Complex.conj_ofReal]
    change ((s^2-1)*‖x‖)^2+2*(((s^2-1:ℝ):ℂ)*inner ℂ x (b • u)).re+
      (‖b‖*‖u‖)^2 = _
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  have hR : ‖x-b • u‖^2 = ‖x‖^2-2*(inner ℂ x (b • u)).re+‖b‖^2*‖u‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ),norm_smul]
    change ‖x‖^2-2*(inner ℂ x (b • u)).re+(‖b‖*‖u‖)^2 = _
    ring
  have hprod := mul_le_mul_of_nonneg_right hproduct (sq_nonneg ‖b‖)
  simp only [mul_pow] at hc2
  rw [hy] at hc2
  have hscaled : (s^2-1)*‖v‖^2*‖x-b • u‖^2 ≤
      (s^2-1)*‖v‖^2*(s^2*‖x‖^2) := by
    rw [hR]
    nlinarith only [hc2,hprod]
  have hbound : ‖x-b • u‖^2 ≤ s^2*‖x‖^2 :=
    (mul_le_mul_iff_right₀ (mul_pos hs2 (sq_pos_of_pos hv0))).mp hscaled
  change ‖x-b • u‖ ≤ s*‖x‖
  nlinarith only [hbound,norm_nonneg (x-b • u),mul_nonneg hs0 (norm_nonneg x)]

end Lemniscate
