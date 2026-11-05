import Lemniscate.ShortInverseSineNorm
import Lemniscate.NeutralHouseholder

/-! Weighted operator bounds for actual Householder maps.  The hypotheses
are norms of the shifted vector and its inverse-weight Fourier image. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private theorem normalized_product_bound (s N W A B D d : ℝ)
    (hN0 : 0 ≤ N) (hW0 : 0 ≤ W) (hN : N ≤ A) (hW : W ≤ B)
    (hD0 : 0 < D) (hd : D ≤ d)
    (hnum : s^2*A^2*B^2 ≤ (s^2+1)^2*D^2) :
    s^2*N^2*(d⁻¹*W)^2 ≤ (s^2+1)^2 := by
  have hd0 : 0 < d := hD0.trans_le hd
  have h : s^2*N^2*W^2 ≤ (s^2+1)^2*d^2 := by
    calc
      _ ≤ s^2*A^2*B^2 := by gcongr
      _ ≤ (s^2+1)^2*D^2 := hnum
      _ ≤ (s^2+1)^2*d^2 := by gcongr
  have he : s^2*N^2*(d⁻¹*W)^2 = (s^2*N^2*W^2)/(d^2) := by
    field_simp
  rw [he]
  exact (div_le_iff₀ (sq_pos_of_pos hd0)).mpr h

private theorem rank_one_data (e a : circleH4Domain T)
    (he : inner ℂ (e : CircleL2 T) (e : CircleL2 T) = 1)
    (ha : inner ℂ (a : CircleL2 T) (a : CircleL2 T) = 1)
    (hea : inner ℂ (a : CircleL2 T) (e : CircleL2 T) =
      inner ℂ (e : CircleL2 T) (a : CircleL2 T))
    (d : ℝ) (hd : 0 < d)
    (hden : 1 + inner ℂ (e : CircleL2 T) (a : CircleL2 T) = (d : ℂ)) :
    let u := e+a
    let v := (d⁻¹ : ℂ) • (u : CircleL2 T)
    inner ℂ v (u : CircleL2 T) = 2 ∧
      ∀ f : circleH4Domain T,
        f-inner ℂ v (f : CircleL2 T) • u = neutralHouseholderDomain e a f := by
  have hs := neutral_householder_sum_inner (e : CircleL2 T) (a : CircleL2 T) he ha hea
  rw [hden] at hs
  constructor
  · change inner ℂ ((d⁻¹ : ℂ) • ((e : CircleL2 T)+(a : CircleL2 T)))
      ((e : CircleL2 T)+(a : CircleL2 T)) = 2
    rw [inner_smul_left, map_inv₀, Complex.conj_ofReal, hs]
    have hdne : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
    field_simp
  · intro f
    simp only [neutralHouseholderDomain, inner_smul_left, map_inv₀,
      Complex.conj_ofReal, hden, Submodule.coe_add]

private theorem inverse_weight_smul_norm (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n)
    (d : ℝ) (hd : 0 < d) (u : CircleL2 T) :
    ‖shortInverseWeightFourier T w hw ((d⁻¹ : ℂ) • u)‖ =
      d⁻¹ * ‖shortInverseWeightFourier T w hw u‖ := by
  have h := (shortInverseWeightFourierCLM T w hw).map_smul (d⁻¹ : ℂ) u
  simp only [short_inverse_fourier_clm_apply] at h
  rw [h, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]

/-- The rational comparisons give both weighted operator bounds for the
actual map, uniformly on the full H4 domain. -/
theorem short_weighted_householder_operator_bounds (e a : circleH4Domain T)
    (he : inner ℂ (e : CircleL2 T) (e : CircleL2 T) = 1)
    (ha : inner ℂ (a : CircleL2 T) (a : CircleL2 T) = 1)
    (hea : inner ℂ (a : CircleL2 T) (e : CircleL2 T) =
      inner ℂ (e : CircleL2 T) (a : CircleL2 T))
    (d : ℝ) (hd : (99/50:ℝ) ≤ d)
    (hden : 1 + inner ℂ (e : CircleL2 T) (a : CircleL2 T) = (d : ℂ))
    (hV : shortVNorm T (e+a) ≤ 17/2)
    (hDV : ‖shortInverseWeightFourier T shortVWeight short_v_weight_one_le
      ((e+a : circleH4Domain T) : CircleL2 T)‖ ≤ 1/2)
    (hH : shortH1Norm T (e+a) ≤ 9/2)
    (hDH : ‖shortInverseWeightFourier T shortH1Weight short_h1_weight_one_le
      ((e+a : circleH4Domain T) : CircleL2 T)‖ ≤ 89/100) :
    ∀ f : circleH4Domain T,
      shortVNorm T (neutralHouseholderDomain e a f) ≤ (3/2:ℝ)*shortVNorm T f ∧
      shortH1Norm T (neutralHouseholderDomain e a f) ≤ (6/5:ℝ)*shortH1Norm T f := by
  have hd0 : 0 < d := (by norm_num : (0:ℝ) < 99/50).trans_le hd
  let u := e+a
  let v := (d⁻¹ : ℂ) • (u : CircleL2 T)
  have hr := rank_one_data T e a he ha hea d hd0 hden
  have hVprod : (3/2:ℝ)^2*shortVNorm T u^2*
      ‖shortInverseWeightFourier T shortVWeight short_v_weight_one_le v‖^2 ≤
        ((3/2:ℝ)^2+1)^2 := by
    rw [inverse_weight_smul_norm T _ _ d hd0]
    exact normalized_product_bound (3/2) _ _ (17/2) (1/2) (99/50) d
      (short_v_norm_nonneg T u) (norm_nonneg _) hV hDV (by norm_num) hd (by norm_num)
  have hHprod : (6/5:ℝ)^2*shortH1Norm T u^2*
      ‖shortInverseWeightFourier T shortH1Weight short_h1_weight_one_le v‖^2 ≤
        ((6/5:ℝ)^2+1)^2 := by
    rw [inverse_weight_smul_norm T _ _ d hd0]
    exact normalized_product_bound (6/5) _ _ (9/2) (89/100) (99/50) d
      (short_h1_norm_nonneg T u) (norm_nonneg _) hH hDH (by norm_num) hd (by norm_num)
  intro f
  have hv := short_v_householder_norm T u v (3/2) (by norm_num) hr.1 hVprod f
  have hh := short_h1_householder_norm T u v (6/5) (by norm_num) hr.1 hHprod f
  rw [hr.2 f] at hv hh
  exact ⟨hv,hh⟩

end Lemniscate
