import Lemniscate.NeutralHouseholder
import Mathlib.Analysis.Seminorm
import Lemniscate.Algebra

/-! The two auxiliary maps are polynomials in the neutral vectors.
Their error bounds do not assume that an intermediate pair is normalized. -/
namespace Lemniscate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def shortRightInput (e ψ u : E) : E := u-inner ℂ (ψ-e) u • e
noncomputable def shortLeftInput (e ψ u : E) : E := u+inner ℂ e u • (ψ-e)

theorem short_right_input_bound (V : Seminorm ℂ E) (e ψ u : E) (X : ℝ)
    (hV : V e ≤ 5) (hz : ‖ψ-e‖ ≤ 51/1000)
    (hu : ‖u‖ ≤ X) (hVu : V u ≤ (3/2:ℝ)*X) :
    V (shortRightInput e ψ u) ≤ 2*X := by
  have hX : 0 ≤ X := (norm_nonneg _).trans hu
  have hb := (norm_inner_le_norm (𝕜 := ℂ) (ψ-e) u).trans
    (mul_le_mul hz hu (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 51/1000))
  have ht := map_sub_le_add V u (inner ℂ (ψ-e) u • e)
  rw [map_smul_eq_mul] at ht
  have hm := mul_le_mul hb hV (apply_nonneg V _) (by positivity : (0:ℝ) ≤ (51/1000)*X)
  change V (u-inner ℂ (ψ-e) u • e) ≤ _
  nlinarith only [ht,hVu,hm,hX]

theorem short_left_input_bound (W : Seminorm ℂ E) (e ψ u : E) (X : ℝ)
    (he : ‖e‖ ≤ 1) (hz : W (ψ-e) ≤ 1/4)
    (hu : ‖u‖ ≤ X) (hWu : W u ≤ (6/5:ℝ)*X) :
    W (shortLeftInput e ψ u) ≤ (3/2:ℝ)*X := by
  have hX : 0 ≤ X := (norm_nonneg _).trans hu
  have hb := (norm_inner_le_norm (𝕜 := ℂ) e u).trans
    (mul_le_mul he hu (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
  simp only [one_mul] at hb
  have ht := map_add_le_add W u (inner ℂ e u • (ψ-e))
  rw [map_smul_eq_mul] at ht
  have hm := mul_le_mul hb hz (apply_nonneg W _) hX
  change W (u+inner ℂ e u • (ψ-e)) ≤ _
  nlinarith only [ht,hWu,hm,hX]

theorem short_right_adjoint_difference (V : Seminorm ℂ E) (e ψ ψ₇ u : E) (ε X : ℝ)
    (hV : V e ≤ 5) (hε : 0 ≤ ε) (hψ : ‖ψ-ψ₇‖ ≤ ε/5) (hu : ‖u‖ ≤ X) :
    V (shortRightInput e ψ u-shortRightInput e ψ₇ u) ≤ ε*X := by
  have hX : 0 ≤ X := (norm_nonneg _).trans hu
  have hid : shortRightInput e ψ u-shortRightInput e ψ₇ u =
      -(inner ℂ (ψ-ψ₇) u • e) := by
    simp only [shortRightInput,inner_sub_left]
    module
  rw [hid,map_neg_eq_map,map_smul_eq_mul]
  have hb := (norm_inner_le_norm (𝕜 := ℂ) (ψ-ψ₇) u).trans
    (mul_le_mul hψ hu (norm_nonneg _) (by positivity : (0:ℝ) ≤ ε/5))
  have hm := mul_le_mul hb hV (apply_nonneg V _) (by positivity : (0:ℝ) ≤ ε/5*X)
  nlinarith only [hm]

theorem short_left_adjoint_difference (W : Seminorm ℂ E) (e ψ ψ₇ u : E) (ε X : ℝ)
    (he : ‖e‖ ≤ 1) (hψ : W (ψ-ψ₇) ≤ ε) (hu : ‖u‖ ≤ X) :
    W (shortLeftInput e ψ u-shortLeftInput e ψ₇ u) ≤ ε*X := by
  have hX : 0 ≤ X := (norm_nonneg _).trans hu
  have hid : shortLeftInput e ψ u-shortLeftInput e ψ₇ u =
      inner ℂ e u • (ψ-ψ₇) := by
    simp only [shortLeftInput]
    module
  rw [hid,map_smul_eq_mul]
  have hb := (norm_inner_le_norm (𝕜 := ℂ) e u).trans
    (mul_le_mul he hu (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
  simp only [one_mul] at hb
  simpa only [mul_comm] using mul_le_mul hb hψ (apply_nonneg W _) hX

theorem short_right_rotation_difference (V : Seminorm ℂ E)
    (e e₇ ψ u u₇ : E) (ε X : ℝ) (hε : 0 ≤ ε) (hX : 0 ≤ X)
    (he : V e ≤ 5) (he₇ : V e₇ ≤ 5) (hz : ‖ψ-e‖ ≤ 51/1000)
    (hδe : V (e-e₇) ≤ ε) (hδe₀ : ‖e-e₇‖ ≤ ε/250)
    (hu₇ : ‖u₇‖ ≤ X)
    (hδu : V (u-u₇) ≤ (11/10:ℝ)*ε*X)
    (hδu₀ : ‖u-u₇‖ ≤ 4*(ε/250)*X) :
    V (shortRightInput e ψ u-shortRightInput e₇ ψ u₇) ≤ (13/10:ℝ)*ε*X := by
  have hid : shortRightInput e ψ u-shortRightInput e₇ ψ u₇ =
      (u-u₇)-inner ℂ (ψ-e) (u-u₇) • e-
      inner ℂ (ψ-e) u₇ • (e-e₇)+inner ℂ (e-e₇) u₇ • e₇ := by
    simp only [shortRightInput,inner_sub_left,inner_sub_right]
    module
  have h1 := (norm_inner_le_norm (𝕜 := ℂ) (ψ-e) (u-u₇)).trans
    (mul_le_mul hz hδu₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 51/1000))
  have h2 := (norm_inner_le_norm (𝕜 := ℂ) (ψ-e) u₇).trans
    (mul_le_mul hz hu₇ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 51/1000))
  have h3 := (norm_inner_le_norm (𝕜 := ℂ) (e-e₇) u₇).trans
    (mul_le_mul hδe₀ hu₇ (norm_nonneg _) (by positivity : (0:ℝ) ≤ ε/250))
  have hb1 := mul_le_mul h1 he (apply_nonneg V _) (by positivity : (0:ℝ) ≤ (51/1000)*(4*(ε/250)*X))
  have hb2 := mul_le_mul h2 hδe (apply_nonneg V _) (by positivity : (0:ℝ) ≤ (51/1000)*X)
  have hb3 := mul_le_mul h3 he₇ (apply_nonneg V _) (by positivity : (0:ℝ) ≤ ε/250*X)
  let a := inner ℂ (ψ-e) (u-u₇) • e
  let b := inner ℂ (ψ-e) u₇ • (e-e₇)
  let c := inner ℂ (e-e₇) u₇ • e₇
  have ht : V ((u-u₇)-a-b+c) ≤ V (u-u₇)+V a+V b+V c := by
    have ht1 := map_sub_le_add V (u-u₇) a
    have ht2 := map_sub_le_add V ((u-u₇)-a) b
    have ht3 := map_add_le_add V ((u-u₇)-a-b) c
    linarith only [ht1,ht2,ht3]
  dsimp only [a,b,c] at ht
  simp only [map_smul_eq_mul] at ht
  rw [hid]
  nlinarith only [ht,hδu,hb1,hb2,hb3,mul_nonneg hε hX]

theorem short_left_rotation_difference (W : Seminorm ℂ E)
    (e e₇ ψ u u₇ : E) (ε X : ℝ) (hε : 0 ≤ ε) (hX : 0 ≤ X)
    (he : ‖e‖ ≤ 1) (he₇ : ‖e₇‖ ≤ 1) (hz : W (ψ-e) ≤ 1/4)
    (hδe : W (e-e₇) ≤ ε/16) (hδe₀ : ‖e-e₇‖ ≤ ε/250)
    (hu₇ : ‖u₇‖ ≤ X)
    (hδu : W (u-u₇) ≤ ((20/19:ℝ)/16+(2925/361)/250)*ε*X)
    (hδu₀ : ‖u-u₇‖ ≤ 4*(ε/250)*X) :
    W (shortLeftInput e ψ u-shortLeftInput e₇ ψ u₇) ≤ (1/6:ℝ)*ε*X := by
  have hid : shortLeftInput e ψ u-shortLeftInput e₇ ψ u₇ =
      (u-u₇)+inner ℂ e (u-u₇) • (ψ-e)+
      inner ℂ (e-e₇) u₇ • (ψ-e)-inner ℂ e₇ u₇ • (e-e₇) := by
    simp only [shortLeftInput,inner_sub_left,inner_sub_right]
    module
  have h1 := (norm_inner_le_norm (𝕜 := ℂ) e (u-u₇)).trans
    (mul_le_mul he hδu₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
  have h2 := (norm_inner_le_norm (𝕜 := ℂ) (e-e₇) u₇).trans
    (mul_le_mul hδe₀ hu₇ (norm_nonneg _) (by positivity : (0:ℝ) ≤ ε/250))
  have h3 := (norm_inner_le_norm (𝕜 := ℂ) e₇ u₇).trans
    (mul_le_mul he₇ hu₇ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
  simp only [one_mul] at h1 h3
  have hb1 := mul_le_mul h1 hz (apply_nonneg W _) (by positivity : (0:ℝ) ≤ 4*(ε/250)*X)
  have hb2 := mul_le_mul h2 hz (apply_nonneg W _) (by positivity : (0:ℝ) ≤ ε/250*X)
  have hb3 := mul_le_mul h3 hδe (apply_nonneg W _) hX
  let a := inner ℂ e (u-u₇) • (ψ-e)
  let b := inner ℂ (e-e₇) u₇ • (ψ-e)
  let c := inner ℂ e₇ u₇ • (e-e₇)
  have ht : W ((u-u₇)+a+b-c) ≤ W (u-u₇)+W a+W b+W c := by
    have ht1 := map_add_le_add W (u-u₇) a
    have ht2 := map_add_le_add W ((u-u₇)+a) b
    have ht3 := map_sub_le_add W ((u-u₇)+a+b) c
    linarith only [ht1,ht2,ht3]
  dsimp only [a,b,c] at ht
  simp only [map_smul_eq_mul] at ht
  rw [hid]
  nlinarith only [ht,hδu,hb1,hb2,hb3,mul_nonneg hε hX]

end Lemniscate
