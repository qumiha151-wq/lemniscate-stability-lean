import Lemniscate.FourierSeries
import Lemniscate.IntervalExtras

/-! Soundness of the actual cosine matrix interval formulas. The coefficients
are the convergent series formulas, conditional on the two parameter boxes.
Identification with the geometric operator remains a separate obligation. -/
namespace Lemniscate.CoarseArithmetic

noncomputable def fourierCoefficient (r q : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then constantCoefficient r q else evenCoefficient r q j

theorem fourier_enclosure (r q : ℝ) (j : ℕ)
    (hr : Contains ⟨rlo,rhi⟩ r) (hq : Contains ⟨qlo,qhi⟩ q) :
    Contains (hInterval j) (fourierCoefficient r q j) := by
  by_cases hj : j = 0
  · subst j
    simpa [fourierCoefficient] using constant_fourier_enclosure r q hr hq
  · simpa [fourierCoefficient, hj] using
      positive_fourier_enclosure r q j hr hq (Nat.pos_of_ne_zero hj)

noncomputable def cosineMatrixEntry (r q : ℝ) (j k : ℕ) : ℝ :=
  let n : ℝ := 2*(j:ℝ)
  let m : ℝ := 2*(k:ℝ)
  if j = 0 ∧ k = 0 then -42
  else if j = 0 ∨ k = 0 then
    (r*fourierCoefficient r q (j+k)*Real.sqrt 2)*(-(15/4:ℝ)*(n+m)^2)
  else
    let nonconstant := r*
      (fourierCoefficient r q (j-k+(k-j))*(45*n*m-(15/4:ℝ)*(n-m)^2)+
       fourierCoefficient r q (j+k)*(-45*n*m-(15/4:ℝ)*(n+m)^2))
    if j = k then nonconstant+(-4*r^2*n^4-42) else nonconstant

theorem cosine_diagonal_enclosure (r : ℝ) (n : ℚ)
    (hr : Contains ⟨rlo,rhi⟩ r) :
    Contains ⟨-4*rhi^2*n^4-42,-4*rlo^2*n^4-42⟩ (-4*r^2*(n:ℝ)^4-42) := by
  have hr0 : 0 ≤ r := (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans hr.1
  have hl : (rlo:ℝ)^2 ≤ r^2 := pow_le_pow_left₀ (by norm_num [rlo]) hr.1 2
  have hu : r^2 ≤ (rhi:ℝ)^2 := pow_le_pow_left₀ hr0 hr.2 2
  have hl' := mul_le_mul_of_nonneg_right hl (by positivity : (0:ℝ) ≤ (n:ℝ)^4)
  have hu' := mul_le_mul_of_nonneg_right hu (by positivity : (0:ℝ) ≤ (n:ℝ)^4)
  constructor <;> simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_neg,
    Rat.cast_ofNat, Rat.cast_pow] <;> linarith

theorem cosine_matrix_enclosure (r q : ℝ) (j k : ℕ)
    (hr : Contains ⟨rlo,rhi⟩ r) (hq : Contains ⟨qlo,qhi⟩ q) :
    Contains (cosineEntry j k) (cosineMatrixEntry r q j k) := by
  by_cases h00 : j = 0 ∧ k = 0
  · simp only [cosineEntry, cosineMatrixEntry, if_pos h00]
    simpa only [Rat.cast_neg, Rat.cast_ofNat] using point_sound (-42)
  by_cases h0 : j = 0 ∨ k = 0
  · simp only [cosineEntry, cosineMatrixEntry, if_neg h00, if_pos h0]
    have h := scale_sound _ _ (-(15/4:ℚ)*(2*(j:ℚ)+2*(k:ℚ))^2)
      (mul_sound _ _ _ _ (mul_sound _ _ _ _ hr (fourier_enclosure r q (j+k) hr hq))
        coarse_sqrt_two)
    simpa only [Rat.cast_neg, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_add, Rat.cast_natCast] using h
  have hminus := scale_sound _ _
    (45*(2*(j:ℚ))*(2*(k:ℚ))-(15/4:ℚ)*(2*(j:ℚ)-2*(k:ℚ))^2)
    (fourier_enclosure r q (j-k+(k-j)) hr hq)
  have hplus := scale_sound _ _
    (-45*(2*(j:ℚ))*(2*(k:ℚ))-(15/4:ℚ)*(2*(j:ℚ)+2*(k:ℚ))^2)
    (fourier_enclosure r q (j+k) hr hq)
  have hnonconstant := mul_sound _ _ _ _ hr (add_sound _ _ _ _ hminus hplus)
  by_cases heq : j = k
  · have h := add_sound _ _ _ _ hnonconstant (cosine_diagonal_enclosure r (2*(j:ℚ)) hr)
    simpa only [cosineEntry, cosineMatrixEntry, if_neg h00, if_neg h0, if_pos heq,
      Rat.cast_neg, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
      Rat.cast_add, Rat.cast_sub, Rat.cast_natCast] using h
  · simpa only [cosineEntry, cosineMatrixEntry, if_neg h00, if_neg h0, if_neg heq,
      Rat.cast_neg, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
      Rat.cast_add, Rat.cast_sub, Rat.cast_natCast] using hnonconstant

end Lemniscate.CoarseArithmetic
