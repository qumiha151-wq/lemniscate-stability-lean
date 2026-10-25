import Lemniscate.NeutralMode

/-! Normalize a proved nonzero neutral vector without introducing a separate
unit-vector assumption in applications to the actual differential operator. -/
namespace Lemniscate
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def normalizedNeutralCoerciveOperator (D : Submodule ℂ E) (A : D →ₗ[ℂ] E)
    (b : D) (hb : (b : E) ≠ 0) (hAb : A b = 0) (gap : ℝ) (hgap : 0 < gap)
    (hd : ∀ w : D, inner ℂ (b : E) (w : E) = 0 →
      (inner ℂ (w : E) (A w)).re ≤ -gap*‖(w : E)‖^2) : NeutralCoerciveOperator E where
  domain := D
  op := A
  neutral := ((‖(b : E)‖:ℂ)⁻¹) • b
  unit_neutral := by
    change ‖((‖(b : E)‖:ℂ)⁻¹) • (b : E)‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hb)]
  kills_neutral := by simp only [map_smul, hAb, smul_zero]
  gap := gap
  gap_pos := hgap
  dissipative := by
    intro w hw
    apply hd w
    change inner ℂ (((‖(b : E)‖:ℂ)⁻¹) • (b : E)) (w : E) = 0 at hw
    rw [inner_smul_left] at hw
    have hn : (‖(b : E)‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb)
    have hc : conj ((‖(b : E)‖:ℂ)⁻¹) ≠ 0 := by
      rw [map_inv₀, Complex.conj_ofReal]
      exact inv_ne_zero hn
    exact (mul_eq_zero.mp hw).resolve_left hc

end Lemniscate
