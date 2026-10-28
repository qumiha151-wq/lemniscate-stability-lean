import Lemniscate.PeriodicSineDerivativeSeries
import Lemniscate.PeriodicSinePolynomialNorm

/-! The full angular H4 truncation error is bounded by the omitted weighted
sine coefficients. The proof keeps every tail term. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

private theorem angular_derivative_tail (f : circleH4Domain T) (v : SineSequenceSpace)
    (hf : (f : CircleL2 T) = circleEvenSineSynthesis T v) (j : Fin 4)
    (hv : Summable (fun n : ℕ => ‖v n‖ * (2*(n+1:ℕ):ℝ)^(j.val+1))) (N : ℕ) :
    (2*Real.pi/T)⁻¹^(j.val+1)*
      ‖circleH4Derivative T j (f-circleSineTrialH4 T N (fun n => v n.val))‖ ≤
        ∑' n : ℕ, ‖v (n+N)‖ * (2*(n+N+1:ℕ):ℝ)^(j.val+1) := by
  have hκ : 0 < 2*Real.pi/T := div_pos (by positivity) (Fact.out : 0 < T)
  have hv' : Summable (fun n : ℕ => ‖v n‖ *
      (2*Real.pi/T*(2*(n+1:ℕ):ℝ))^(j.val+1)) := by
    simpa only [mul_pow,mul_left_comm,mul_assoc] using hv.mul_left ((2*Real.pi/T)^(j.val+1))
  have h := circle_sine_truncation_derivative_error T f v hf j hv' N
  have ht : (∑' n : ℕ, ‖v (n+N)‖ *
      (2*Real.pi/T*(2*(n+N+1:ℕ):ℝ))^(j.val+1)) =
      (2*Real.pi/T)^(j.val+1) *
        ∑' n : ℕ, ‖v (n+N)‖ * (2*(n+N+1:ℕ):ℝ)^(j.val+1) := by
    simp only [mul_pow,mul_left_comm ‖v _‖,mul_assoc,tsum_mul_left]
  rw [ht] at h
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg (inv_nonneg.mpr hκ.le) (j.val+1))
  simpa only [inv_pow,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hκ.ne'),one_mul] using hh

theorem circle_sine_truncation_h4_error (f : circleH4Domain T) (v : SineSequenceSpace)
    (hf : (f : CircleL2 T) = circleEvenSineSynthesis T v)
    (hv : ∀ k : Fin 5, Summable (fun n : ℕ => ‖v n‖ * (2*(n+1:ℕ):ℝ)^k.val)) (N : ℕ) :
    circleAngularH4Norm T (f-circleSineTrialH4 T N (fun n => v n.val)) ≤
      ∑ k : Fin 5, ∑' n : ℕ, ‖v (n+N)‖ * (2*(n+N+1:ℕ):ℝ)^k.val := by
  have h0 := circle_sine_truncation_l2_error T v
    (by simpa only [Fin.val_zero,pow_zero,mul_one] using hv ⟨0,by decide⟩) N
  have h1 := angular_derivative_tail T f v hf ⟨0,by decide⟩ (hv ⟨1,by decide⟩) N
  have h2 := angular_derivative_tail T f v hf ⟨1,by decide⟩ (hv ⟨2,by decide⟩) N
  have h3 := angular_derivative_tail T f v hf ⟨2,by decide⟩ (hv ⟨3,by decide⟩) N
  have h4 := angular_derivative_tail T f v hf ⟨3,by decide⟩ (hv ⟨4,by decide⟩) N
  rw [← hf] at h0
  change ‖((f-circleSineTrialH4 T N (fun n => v n.val)) : CircleL2 T)‖ ≤ _ at h0
  change (2*Real.pi/T)⁻¹^1 *
    ‖(circleH4Jet T (f-circleSineTrialH4 T N (fun n => v n.val))).first‖ ≤ _ at h1
  change (2*Real.pi/T)⁻¹^2 *
    ‖(circleH4Jet T (f-circleSineTrialH4 T N (fun n => v n.val))).second‖ ≤ _ at h2
  change (2*Real.pi/T)⁻¹^3 *
    ‖(circleH4Jet T (f-circleSineTrialH4 T N (fun n => v n.val))).third‖ ≤ _ at h3
  change (2*Real.pi/T)⁻¹^4 *
    ‖(circleH4Jet T (f-circleSineTrialH4 T N (fun n => v n.val))).fourth‖ ≤ _ at h4
  simp only [Fin.val_mk,zero_add,Nat.reduceAdd,pow_one] at h1 h2 h3 h4
  simpa [circleAngularH4Norm,Fin.sum_univ_succ,add_assoc] using
    add_le_add (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) h4

end Lemniscate
