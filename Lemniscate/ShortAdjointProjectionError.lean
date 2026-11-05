import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! Normalizing an actual orthogonal truncation costs the square of its L2
tail.  Re-normalizing the adjoint is controlled by its exact phase pairing.
These estimates avoid high-precision normalization constants. -/
namespace Lemniscate
open Complex
open scoped ComplexConjugate

theorem short_normalized_projection_error
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e g : H) (P : Seminorm ℂ H) (δ B C : ℝ)
    (he : ‖e‖ = 1) (hg : 0 < ‖g‖)
    (hinner : (inner ℂ g e).re = ‖g‖^2)
    (htail : ‖e-g‖ ≤ δ) (hδ : 0 ≤ δ)
    (hB : P (e-g) ≤ B) (hC : 0 ≤ C)
    (hN : P ((‖g‖:ℂ)⁻¹ • g) ≤ C) :
    P (e-(‖g‖:ℂ)⁻¹ • g) ≤ B+δ^2*C := by
  let n := (‖g‖:ℂ)⁻¹ • g
  have hs : ‖e-g‖^2 = 1-‖g‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ),he]
    change (1:ℝ)^2-2*(inner ℂ e g).re+‖g‖^2 = 1-‖g‖^2
    have hi : (inner ℂ e g).re = (inner ℂ g e).re := inner_re_symm (𝕜 := ℂ) e g
    rw [hi,hinner]
    ring
  have ht : ‖g‖ ≤ 1 := by nlinarith [sq_nonneg ‖e-g‖,norm_nonneg g]
  have htail2 := pow_le_pow_left₀ (norm_nonneg (e-g)) htail 2
  have hnorm : 1-‖g‖ ≤ δ^2 := by
    nlinarith [mul_nonneg (norm_nonneg g) (sub_nonneg.mpr ht)]
  have hng : (‖g‖:ℂ) • n = g := by
    dsimp only [n]
    rw [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hg.ne'),one_smul]
  have heq : e-n = (e-g)+((‖g‖-1:ℝ):ℂ) • n := by
    calc
      _ = (e-(‖g‖:ℂ) • n)+((‖g‖-1:ℝ):ℂ) • n := by
        push_cast
        module
      _ = _ := by rw [hng]
  change P (e-n) ≤ _
  rw [heq]
  calc
    _ ≤ P (e-g)+P (((‖g‖-1:ℝ):ℂ) • n) := map_add_le_add P _ _
    _ = P (e-g)+(1-‖g‖)*P n := by
      rw [map_smul_eq_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr ht)]
      ring
    _ ≤ B+(1-‖g‖)*C := add_le_add hB
      (mul_le_mul_of_nonneg_left hN (sub_nonneg.mpr ht))
    _ ≤ B+δ^2*C := by linarith [mul_le_mul_of_nonneg_right hnorm hC]

theorem short_adjoint_truncated_pairing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (p e eN g : H) (t : ℝ)
    (hp : inner ℂ p e = 1) (hproj : inner ℂ (p-g) eN = 0)
    (ht : inner ℂ g eN = (t:ℂ)) :
    |1-t| ≤ ‖p‖*‖e-eN‖ := by
  have hi : inner ℂ p (eN-e) = ((t-1:ℝ):ℂ) := by
    rw [inner_sub_left] at hproj
    rw [inner_sub_right,hp]
    push_cast
    linear_combination hproj+ht
  have h := norm_inner_le_norm (𝕜 := ℂ) p (eN-e)
  rw [hi,Complex.norm_real,Real.norm_eq_abs,norm_sub_rev] at h
  simpa only [abs_sub_comm] using h

theorem short_adjoint_renormalization_error
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ p g pN : H) (t : ℝ) (P : Seminorm ℂ H)
    (A B C δ : ℝ) (hg : g = (t:ℂ) • pN)
    (hA : P (ψ-p) ≤ A) (hB : P (p-g) ≤ B)
    (hC : P pN ≤ C) (hδ : |1-t| ≤ δ) (hδ0 : 0 ≤ δ) :
    P (ψ-pN) ≤ A+B+δ*C := by
  have heq : ψ-pN = (ψ-p)+(p-g)+((t-1:ℝ):ℂ) • pN := by
    rw [hg]
    push_cast
    module
  rw [heq]
  have htri := map_add_le_add P ((ψ-p)+(p-g)) (((t-1:ℝ):ℂ) • pN)
  have htri2 := map_add_le_add P (ψ-p) (p-g)
  rw [map_smul_eq_mul,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm] at htri
  have hm := mul_le_mul hδ hC (apply_nonneg P pN) hδ0
  linarith

end Lemniscate
