import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Weighted sequence Cauchy--Schwarz for the genuine infinite residual.
The two l2 vectors are constructed here; weighted duality is not assumed. -/
namespace Lemniscate
open Complex
open scoped ENNReal ComplexConjugate

theorem short_adjoint_weighted_sequence_duality {ι : Type*}
    (weight : ι → ℝ) (hw : ∀ i, 0 < weight i) (x y : ι → ℂ)
    (hx : Summable (fun i => weight i * ‖x i‖^2))
    (hy : Summable (fun i => ‖y i‖^2 / weight i)) :
    Summable (fun i => inner ℂ (x i) (y i)) ∧
      |(∑' i, inner ℂ (x i) (y i)).re| ≤
        Real.sqrt (∑' i, weight i * ‖x i‖^2) *
          Real.sqrt (∑' i, ‖y i‖^2 / weight i) := by
  have hroot (i : ι) : Real.sqrt (weight i) ≠ 0 :=
    (Real.sqrt_pos.mpr (hw i)).ne'
  have hnX (i : ι) :
      ‖(Real.sqrt (weight i):ℂ) * x i‖^2 = weight i * ‖x i‖^2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hw i).le]
  have hnY (i : ι) :
      ‖(Real.sqrt (weight i):ℂ)⁻¹ * y i‖^2 = ‖y i‖^2 / weight i := by
    rw [norm_mul, mul_pow, norm_inv, inv_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hw i).le]
    ring
  have hX : Memℓp (fun i => (Real.sqrt (weight i):ℂ) * x i) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hnX] using hx
  have hY : Memℓp (fun i => (Real.sqrt (weight i):ℂ)⁻¹ * y i) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hnY] using hy
  let X : lp (fun _ : ι => ℂ) 2 := ⟨_,hX⟩
  let Y : lp (fun _ : ι => ℂ) 2 := ⟨_,hY⟩
  have hi (i : ι) : inner ℂ (X i) (Y i) = inner ℂ (x i) (y i) := by
    change inner ℂ ((Real.sqrt (weight i):ℂ) • x i)
      ((Real.sqrt (weight i):ℂ)⁻¹ • y i) = _
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hroot i)), one_mul]
  have hnormX : ‖X‖^2 = ∑' i, weight i * ‖x i‖^2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) X
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, X, hnX] using h
  have hnormY : ‖Y‖^2 = ∑' i, ‖y i‖^2 / weight i := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) Y
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Y, hnY] using h
  have hs : Summable (fun i => inner ℂ (x i) (y i)) := by
    exact (lp.summable_inner X Y).congr (fun i => hi i)
  have hinner : (∑' i, inner ℂ (x i) (y i)) = inner ℂ X Y := by
    calc
      _ = ∑' i, inner ℂ (X i) (Y i) := tsum_congr (fun i => (hi i).symm)
      _ = _ := (lp.inner_eq_tsum X Y).symm
  refine ⟨hs, ?_⟩
  rw [hinner, ← hnormX, ← hnormY]
  simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm X Y)

end Lemniscate
