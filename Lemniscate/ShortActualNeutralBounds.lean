import Lemniscate.ShortHouseholderDifference
import Lemniscate.ShortNeutralComparison

/-! The complete neutral-input telescope, with separate L2, H1 and V
errors.  The actual periodic application restricts the ambient space to its
even Fourier submodule. -/
namespace Lemniscate
open Complex

theorem short_neutral_telescope_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V W : Seminorm ℂ E) (e e₇ ψ ψ₇ a : E) (ε η : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hdom : ∀ x, ‖x‖ ≤ V x) (hWV : ∀ x, W x ≤ V x)
    (he : ‖e‖ ≤ 1) (he₇ : ‖e₇‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hVe : V e ≤ 5) (hVe₇ : V e₇ ≤ 5) (hVa : V a ≤ 4) (hWa : W a ≤ 5/2)
    (hz : W (ψ-e) ≤ 1/4)
    (hz₇₀ : ‖ψ₇-e₇‖ ≤ 1/20) (hz₇ : W (ψ₇-e₇) ≤ 11/50)
    (hδe₀ : ‖e-e₇‖ ≤ ε/250) (hδeW : W (e-e₇) ≤ ε/16)
    (hδeV : V (e-e₇) ≤ ε)
    (hδψ₀ : ‖ψ-ψ₇‖ ≤ η/5) (hδψW : W (ψ-ψ₇) ≤ η)
    (hεsmall : ε ≤ 1/160000)
    (hd : (19/10:ℝ) ≤ ‖1+inner ℂ e a‖)
    (hd₇ : (19/10:ℝ) ≤ ‖1+inner ℂ e₇ a‖)
    (hU₀ : ∀ x, ‖neutralHouseholder e a x‖ ≤ V x)
    (hU₇₀ : ∀ x, ‖neutralHouseholder e₇ a x‖ ≤ V x)
    (hUV : ∀ x, V (neutralHouseholder e a x) ≤ (3/2:ℝ)*V x)
    (hU₇V : ∀ x, V (neutralHouseholder e₇ a x) ≤ (3/2:ℝ)*V x)
    (hUW : ∀ x, W (neutralHouseholder e a x) ≤ (6/5:ℝ)*W x)
    (hU₇W : ∀ x, W (neutralHouseholder e₇ a x) ≤ (6/5:ℝ)*W x) :
    let U := neutralHouseholder e a
    let U₇ := neutralHouseholder e₇ a
    let R := fun x => shortRightInput e ψ (U x)
    let L := fun x => shortLeftInput e ψ (U x)
    let Rm := fun x => shortRightInput e ψ₇ (U x)
    let Lm := fun x => shortLeftInput e ψ₇ (U x)
    let R₇ := fun x => shortRightInput e₇ ψ₇ (U₇ x)
    let L₇ := fun x => shortLeftInput e₇ ψ₇ (U₇ x)
    ∀ x, V (U x-U₇ x) ≤ (11/10:ℝ)*ε*V x ∧
      W (L x) ≤ (3/2:ℝ)*V x ∧ V (Rm x) ≤ 2*V x ∧
      W (Lm x) ≤ (3/2:ℝ)*V x ∧ V (R₇ x) ≤ 2*V x ∧
      V (R x-Rm x) ≤ η*V x ∧ W (L x-Lm x) ≤ η*V x ∧
      V (Rm x-R₇ x) ≤ (13/10:ℝ)*ε*V x ∧
      W (Lm x-L₇ x) ≤ (1/6:ℝ)*ε*V x := by
  dsimp only
  have hK : V (e₇+a) ≤ 9 := by
    linarith only [map_add_le_add V e₇ a,hVe₇,hVa]
  have hKW : W (e₇+a) ≤ 15/2 := by
    linarith only [map_add_le_add W e₇ a,hWV e₇,hVe₇,hWa]
  have hK₀ : ‖e₇+a‖ ≤ 2 := by linarith only [norm_add_le e₇ a,he₇,ha]
  have hzm₀ : ‖ψ₇-e‖ ≤ 51/1000 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub ψ₇ e₇ e
    rw [norm_sub_rev e₇ e] at ht
    linarith only [ht,hz₇₀,hδe₀,hεsmall]
  have hzm : W (ψ₇-e) ≤ 1/4 := by
    have hid : ψ₇-e = (ψ₇-e₇)-(e-e₇) := by abel
    rw [hid]
    have ht := map_sub_le_add W (ψ₇-e₇) (e-e₇)
    linarith only [ht,hz₇,hδeW,hεsmall]
  intro x
  let u := neutralHouseholder e a x
  let u₇ := neutralHouseholder e₇ a x
  have hX : 0 ≤ V x := apply_nonneg V x
  have hδU := short_householder_difference V e e₇ a x ε (ε/250) 9
    he he₇ ha hδeV hδe₀ hK hd hd₇
  have hδUW := short_householder_difference W e e₇ a x (ε/16) (ε/250) (15/2)
    he he₇ ha hδeW hδe₀ hKW hd hd₇
  have hδU₀ := short_householder_difference (normSeminorm ℂ E) e e₇ a x
    (ε/250) (ε/250) 2 he he₇ ha hδe₀ hδe₀ hK₀ hd hd₇
  have hUVδ : V (u-u₇) ≤ (11/10:ℝ)*ε*V x := by
    have hm := mul_le_mul_of_nonneg_left (hdom x)
      (by positivity : (0:ℝ) ≤ (20/19)*ε+(390/361)*9*(ε/250))
    nlinarith only [hδU,hm,mul_nonneg hε hX]
  have hUWδ : W (u-u₇) ≤ ((20/19:ℝ)/16+(2925/361)/250)*ε*V x := by
    have hm := mul_le_mul_of_nonneg_left (hdom x)
      (by positivity : (0:ℝ) ≤ (20/19)*(ε/16)+(390/361)*(15/2)*(ε/250))
    nlinarith only [hδUW,hm]
  have hU₀δ : ‖u-u₇‖ ≤ 4*(ε/250)*V x := by
    change ‖u-u₇‖ ≤ _ at hδU₀
    have hm := mul_le_mul_of_nonneg_left (hdom x)
      (by positivity : (0:ℝ) ≤ (20/19)*(ε/250)+(390/361)*2*(ε/250))
    nlinarith only [hδU₀,hm,mul_nonneg hε hX]
  have hUW' : W u ≤ (6/5:ℝ)*V x :=
    (hUW x).trans (mul_le_mul_of_nonneg_left (hWV x) (by norm_num))
  have hU₇W' : W u₇ ≤ (6/5:ℝ)*V x :=
    (hU₇W x).trans (mul_le_mul_of_nonneg_left (hWV x) (by norm_num))
  refine ⟨hUVδ,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact short_left_input_bound W e ψ u (V x) he hz (hU₀ x) hUW'
  · exact short_right_input_bound V e ψ₇ u (V x) hVe hzm₀ (hU₀ x) (hUV x)
  · exact short_left_input_bound W e ψ₇ u (V x) he hzm (hU₀ x) hUW'
  · exact short_right_input_bound V e₇ ψ₇ u₇ (V x) hVe₇
      (hz₇₀.trans (by norm_num)) (hU₇₀ x) (hU₇V x)
  · exact short_right_adjoint_difference V e ψ ψ₇ u η (V x) hVe hη hδψ₀ (hU₀ x)
  · exact short_left_adjoint_difference W e ψ ψ₇ u η (V x) he hδψW (hU₀ x)
  · exact short_right_rotation_difference V e e₇ ψ₇ u u₇ ε (V x) hε hX hVe hVe₇
      hzm₀ hδeV hδe₀ (hU₇₀ x) hUVδ hU₀δ
  · exact short_left_rotation_difference W e e₇ ψ₇ u u₇ ε (V x) hε hX he he₇
      hzm hδeW hδe₀ (hU₇₀ x) hUWδ hU₀δ

end Lemniscate
