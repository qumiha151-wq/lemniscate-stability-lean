import Lemniscate.PeriodicEvenHighSquare

/-! Coarse estimates for the four actual rank-one terms. These use ordinary
L2 norms of the input and avoid weighted projection estimates. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem inner_inverse_norm_bound (u f : CircleL2 T) (d : ℂ)
    (hu : ‖u‖ ≤ 2) (hd : 1 ≤ ‖d‖) : ‖d⁻¹*inner ℂ u f‖ ≤ 2*‖f‖ := by
  have hi : ‖d⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hd
    simpa only [one_div,inv_one] using h
  have hb : ‖inner ℂ u f‖ ≤ 2*‖f‖ :=
    (norm_inner_le_norm u f).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg f))
  rw [norm_mul]
  exact (mul_le_mul hi hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem four_rank_terms_high_bound (u e z f U V : circleH4Domain T)
    (A B : circleH4Domain T →ₗ[ℂ] CircleL2 T) (d : ℂ) (ε : ℝ)
    (hd : 1 ≤ ‖d‖) (hu : ‖u‖ ≤ 2) (he : ‖e‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (hU : ‖U‖ = ‖f‖) (hV : ‖V‖ = ‖f‖)
    (hAu : circleEvenHighSquare T (A u) ≤ 4*ε^2)
    (hBu : circleEvenHighSquare T (B u) ≤ 4*ε^2)
    (hBz : circleEvenHighSquare T (B z) ≤ ε^2)
    (hAe : circleEvenHighSquare T (A e) ≤ ε^2) :
    circleEvenHighSquare T
      ((-(1/2:ℂ)*(conj d)⁻¹*inner ℂ (u:CircleL2 T) (f:CircleL2 T)) • B u+
       (-(1/2:ℂ)*d⁻¹*inner ℂ (u:CircleL2 T) (f:CircleL2 T)) • A u+
       ((1/2:ℂ)*inner ℂ (e:CircleL2 T) (V:CircleL2 T)) • B z+
       (-(1/2:ℂ)*inner ℂ (z:CircleL2 T) (U:CircleL2 T)) • A e) ≤ 49*ε^2*‖f‖^2 := by
  have hb (d' : ℂ) (hd' : 1 ≤ ‖d'‖) :
      ‖-(1/2:ℂ)*d'⁻¹*inner ℂ (u:CircleL2 T) (f:CircleL2 T)‖ ≤ ‖f‖ := by
    rw [mul_assoc,norm_mul]
    have hhalf : ‖-(1/2:ℂ)‖ = (1/2:ℝ) := by norm_num
    rw [hhalf]
    have h := inner_inverse_norm_bound T (u:CircleL2 T) (f:CircleL2 T) d' hu hd'
    simp only [Submodule.norm_coe] at h
    linarith only [h]
  have hbe : ‖inner ℂ (e:CircleL2 T) (V:CircleL2 T)‖ ≤ ‖f‖ := by
    have h := (norm_inner_le_norm (𝕜 := ℂ) (e:CircleL2 T) (V:CircleL2 T)).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg V))
    simpa only [one_mul,Submodule.norm_coe,hV] using h
  have hbz : ‖inner ℂ (z:CircleL2 T) (U:CircleL2 T)‖ ≤ ‖f‖ := by
    have h := (norm_inner_le_norm (𝕜 := ℂ) (z:CircleL2 T) (U:CircleL2 T)).trans
      (mul_le_mul_of_nonneg_right hz (norm_nonneg U))
    simpa only [one_mul,Submodule.norm_coe,hU] using h
  have hc3 : ‖(1/2:ℂ)*inner ℂ (e:CircleL2 T) (V:CircleL2 T)‖ ≤ ‖f‖ := by
    rw [norm_mul]
    norm_num
    simp only [Submodule.norm_coe] at hbe ⊢
    linarith only [hbe,norm_nonneg f]
  have hc4 : ‖-(1/2:ℂ)*inner ℂ (z:CircleL2 T) (U:CircleL2 T)‖ ≤ ‖f‖ := by
    rw [norm_mul]
    norm_num
    simp only [Submodule.norm_coe] at hbz ⊢
    linarith only [hbz,norm_nonneg f]
  have h1 := circle_even_high_square_scaled_bound T _ (B u) ‖f‖ (4*ε^2)
    (hb (conj d) (by simpa only [Complex.norm_conj] using hd)) hBu
  have h2 := circle_even_high_square_scaled_bound T _ (A u) ‖f‖ (4*ε^2) (hb d hd) hAu
  have h3 := circle_even_high_square_scaled_bound T _ (B z) ‖f‖ (ε^2) hc3 hBz
  have h4 := circle_even_high_square_scaled_bound T _ (A e) ‖f‖ (ε^2) hc4 hAe
  have hsum := circle_even_high_square_four_terms T
    ((-(1/2:ℂ)*(conj d)⁻¹*inner ℂ (u:CircleL2 T) (f:CircleL2 T)) • B u)
    ((-(1/2:ℂ)*d⁻¹*inner ℂ (u:CircleL2 T) (f:CircleL2 T)) • A u)
    (((1/2:ℂ)*inner ℂ (e:CircleL2 T) (V:CircleL2 T)) • B z)
    ((-(1/2:ℂ)*inner ℂ (z:CircleL2 T) (U:CircleL2 T)) • A e)
  nlinarith only [hsum,h1,h2,h3,h4,mul_nonneg (sq_nonneg ε) (sq_nonneg ‖f‖)]

end Lemniscate
