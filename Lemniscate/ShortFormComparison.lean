import Lemniscate.Algebra
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Complex.Basic

/-! Bilinear error estimates in the two different low-order norms.
The subtraction identities apply equally to complex sesquilinear forms. -/
namespace Lemniscate

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem short_form_difference_bound (V W : Seminorm ℂ E) (B : E → E → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hleft : ∀ x y z, B (x-y) z = B x z-B y z)
    (hright : ∀ x y z, B x (y-z) = B x y-B x z)
    (hB : ∀ x y, ‖B x y‖ ≤ C*V x*W y) (x x' y y' : E) :
    ‖B x y-B x' y'‖ ≤ C*(V (x-x')*W y+V x'*W (y-y')) := by
  have hid : B x y-B x' y' = B (x-x') y+B x' (y-y') := by
    rw [hleft,hright]
    ring
  rw [hid]
  have ht := norm_add_le (B (x-x') y) (B x' (y-y'))
  linarith only [ht,hB (x-x') y,hB x' (y-y')]

theorem short_symmetric_form_comparison (V : Seminorm ℂ E) (B : E → E → ℂ)
    (hleft : ∀ x y z, B (x-y) z = B x z-B y z)
    (hright : ∀ x y z, B x (y-z) = B x y-B x z)
    (hB : ∀ x y, ‖B x y‖ ≤ 60*V x*V y)
    (U U' : E → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hU : ∀ x, V (U x) ≤ (3/2:ℝ)*V x)
    (hU' : ∀ x, V (U' x) ≤ (3/2:ℝ)*V x)
    (hδ : ∀ x, V (U x-U' x) ≤ (11/10:ℝ)*ε*V x) (x y : E) :
    ‖B (U x) (U y)-B (U' x) (U' y)‖ ≤ 198*ε*V x*V y := by
  have ht := short_form_difference_bound V V B 60 (by norm_num)
    hleft hright hB (U x) (U' x) (U y) (U' y)
  have h1 := mul_le_mul (hδ x) (hU y) (apply_nonneg V _) (by positivity : (0:ℝ) ≤ (11/10)*ε*V x)
  have h2 := mul_le_mul (hU' x) (hδ y) (apply_nonneg V _) (by positivity : (0:ℝ) ≤ (3/2)*V x)
  nlinarith only [ht,h1,h2]

theorem short_positive_form_comparison (V W : Seminorm ℂ E) (B : E → E → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hleft : ∀ x y z, B (x-y) z = B x z-B y z)
    (hright : ∀ x y z, B x (y-z) = B x y-B x z)
    (hB : ∀ x y, ‖B x y‖ ≤ C*V x*W y)
    (R L Rm Lm R' L' : E → E) (ε εψ : ℝ) (hε : 0 ≤ ε) (hεψ : 0 ≤ εψ)
    (hL : ∀ x, W (L x) ≤ (3/2:ℝ)*V x)
    (hRm : ∀ x, V (Rm x) ≤ 2*V x)
    (hLm : ∀ x, W (Lm x) ≤ (3/2:ℝ)*V x)
    (hR' : ∀ x, V (R' x) ≤ 2*V x)
    (hδRψ : ∀ x, V (R x-Rm x) ≤ εψ*V x)
    (hδLψ : ∀ x, W (L x-Lm x) ≤ εψ*V x)
    (hδRe : ∀ x, V (Rm x-R' x) ≤ (13/10:ℝ)*ε*V x)
    (hδLe : ∀ x, W (Lm x-L' x) ≤ (1/6:ℝ)*ε*V x) (x y : E) :
    ‖B (R x) (L y)-B (R' x) (L' y)‖ ≤
      C*((7/3:ℝ)*ε+4*εψ)*V x*V y := by
  have hψ := short_form_difference_bound V W B C hC hleft hright hB
    (R x) (Rm x) (L y) (Lm y)
  have he := short_form_difference_bound V W B C hC hleft hright hB
    (Rm x) (R' x) (Lm y) (L' y)
  have h1 := mul_le_mul (hδRψ x) (hL y) (apply_nonneg W _) (by positivity : (0:ℝ) ≤ εψ*V x)
  have h2 := mul_le_mul (hRm x) (hδLψ y) (apply_nonneg W _) (by positivity : (0:ℝ) ≤ 2*V x)
  have h3 := mul_le_mul (hδRe x) (hLm y) (apply_nonneg W _) (by positivity : (0:ℝ) ≤ (13/10)*ε*V x)
  have h4 := mul_le_mul (hR' x) (hδLe y) (apply_nonneg W _) (by positivity : (0:ℝ) ≤ 2*V x)
  have h12 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
  have h34 := mul_le_mul_of_nonneg_left (add_le_add h3 h4) hC
  have ht := norm_sub_le_norm_sub_add_norm_sub (B (R x) (L y)) (B (Rm x) (Lm y)) (B (R' x) (L' y))
  have hp : 0 ≤ C*ε*V x*V y := by positivity
  have hpψ : 0 ≤ C*εψ*V x*V y := by positivity
  nlinarith only [hψ,he,h12,h34,ht,hp,hpψ]

end Lemniscate
