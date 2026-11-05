import Lemniscate.NeutralHouseholder
import Mathlib.Analysis.Seminorm
import Lemniscate.Algebra

/-! One perturbation formula works in the L2, H1, and V seminorms.
Only the vector errors and a denominator lower bound enter. -/
namespace Lemniscate

theorem short_householder_difference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (N : Seminorm ℂ E) (e e₇ a x : E) (ε ε₀ K : ℝ)
    (he : ‖e‖ ≤ 1) (he₇ : ‖e₇‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (herror : N (e-e₇) ≤ ε) (herror₀ : ‖e-e₇‖ ≤ ε₀)
    (hK : N (e₇+a) ≤ K)
    (hd : (19/10:ℝ) ≤ ‖1+inner ℂ e a‖)
    (hd₇ : (19/10:ℝ) ≤ ‖1+inner ℂ e₇ a‖) :
    N (neutralHouseholder e a x-neutralHouseholder e₇ a x) ≤
      ((20/19:ℝ)*ε+(390/361:ℝ)*K*ε₀)*‖x‖ := by
  have hε : 0 ≤ ε := (apply_nonneg N _).trans herror
  have hε₀ : 0 ≤ ε₀ := (norm_nonneg _).trans herror₀
  have hK₀ : 0 ≤ K := (apply_nonneg N _).trans hK
  let d := 1+inner ℂ e a
  let d₇ := 1+inner ℂ e₇ a
  let b := d⁻¹*inner ℂ (e+a) x
  let b₇ := d₇⁻¹*inner ℂ (e₇+a) x
  have hu : ‖e+a‖ ≤ 2 := by linarith only [norm_add_le e a,he,ha]
  have hu₇ : ‖e₇+a‖ ≤ 2 := by linarith only [norm_add_le e₇ a,he₇,ha]
  have hdpos : 0 < ‖d‖ := by dsimp only [d]; linarith only [hd]
  have hd₇pos : 0 < ‖d₇‖ := by dsimp only [d₇]; linarith only [hd₇]
  have hd0 : d ≠ 0 := norm_pos_iff.mp hdpos
  have hd₇0 : d₇ ≠ 0 := norm_pos_iff.mp hd₇pos
  have hdi : ‖d⁻¹‖ ≤ (10/19:ℝ) := by
    rw [norm_inv]
    exact (inv_le_comm₀ hdpos (by norm_num)).mpr (by norm_num [d]; exact hd)
  have hd₇i : ‖d₇⁻¹‖ ≤ (10/19:ℝ) := by
    rw [norm_inv]
    exact (inv_le_comm₀ hd₇pos (by norm_num)).mpr (by norm_num [d₇]; exact hd₇)
  have hdd : ‖d-d₇‖ ≤ ε₀ := by
    have hid : d-d₇ = inner ℂ (e-e₇) a := by
      simp only [d,d₇,inner_sub_left]
      ring
    rw [hid]
    exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
      ((mul_le_mul herror₀ ha (norm_nonneg _) hε₀).trans_eq (mul_one ε₀))
  have hdiδ : ‖d⁻¹-d₇⁻¹‖ ≤ (100/361:ℝ)*ε₀ := by
    have hid : d⁻¹-d₇⁻¹ = d⁻¹*(d₇-d)*d₇⁻¹ := by field_simp
    rw [hid,norm_mul,norm_mul,norm_sub_rev d₇ d]
    have hm := mul_le_mul hdi hdd (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 10/19)
    have hn := mul_le_mul hm hd₇i (norm_nonneg _) (by positivity : (0:ℝ) ≤ (10/19)*ε₀)
    nlinarith only [hn]
  have hb : ‖b‖ ≤ (20/19:ℝ)*‖x‖ := by
    have hi := (norm_inner_le_norm (𝕜 := ℂ) (e+a) x).trans
      (mul_le_mul_of_nonneg_right hu (norm_nonneg x))
    have hm := mul_le_mul hdi hi (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 10/19)
    change ‖d⁻¹*inner ℂ (e+a) x‖ ≤ _
    rw [norm_mul]
    nlinarith only [hm]
  have hbδ : ‖b-b₇‖ ≤ (390/361:ℝ)*ε₀*‖x‖ := by
    have hid : b-b₇ = d⁻¹*inner ℂ (e-e₇) x+
        (d⁻¹-d₇⁻¹)*inner ℂ (e₇+a) x := by
      simp only [b,b₇,inner_sub_left,inner_add_left]
      ring
    have hi := (norm_inner_le_norm (𝕜 := ℂ) (e-e₇) x).trans
      (mul_le_mul_of_nonneg_right herror₀ (norm_nonneg x))
    have hi₇ := (norm_inner_le_norm (𝕜 := ℂ) (e₇+a) x).trans
      (mul_le_mul_of_nonneg_right hu₇ (norm_nonneg x))
    have h1 := mul_le_mul hdi hi (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 10/19)
    have h2 := mul_le_mul hdiδ hi₇ (norm_nonneg _) (by positivity : (0:ℝ) ≤ (100/361)*ε₀)
    rw [hid]
    have ht := norm_add_le (d⁻¹*inner ℂ (e-e₇) x)
      ((d⁻¹-d₇⁻¹)*inner ℂ (e₇+a) x)
    simp only [norm_mul] at ht
    nlinarith only [ht,h1,h2]
  have hid : neutralHouseholder e a x-neutralHouseholder e₇ a x =
      -(b • (e-e₇))-(b-b₇) • (e₇+a) := by
    dsimp only [neutral_householder_apply,b,b₇,d,d₇]
    rw [neutral_householder_apply,neutral_householder_apply]
    module
  rw [hid]
  have ht := map_sub_le_add N (-(b • (e-e₇))) ((b-b₇) • (e₇+a))
  simp only [map_neg_eq_map,map_smul_eq_mul] at ht
  have h1 := mul_le_mul hb herror (apply_nonneg N _) (by positivity : (0:ℝ) ≤ (20/19)*‖x‖)
  have h2 := mul_le_mul hbδ hK (apply_nonneg N _) (by positivity : (0:ℝ) ≤ (390/361)*ε₀*‖x‖)
  nlinarith only [ht,h1,h2]

end Lemniscate
