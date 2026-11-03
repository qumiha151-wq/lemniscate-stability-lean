import Lemniscate.WeierstrassRows
import Mathlib.NumberTheory.ZetaValues

/-! Evaluation of the real integer row by splitting the square series
into even and odd terms. -/
namespace Lemniscate
open Complex

private theorem inverse_square_integer_rows (B : ℝ)
    (hB : HasSum (fun n : ℕ => 1/(n:ℝ)^2) B) :
    HasSum (fun m : ℤ => 1/((1/2:ℝ)+(m:ℝ))^2) (6*B) ∧
      HasSum (fun m : ℤ => 1/(m:ℝ)^2) (2*B) := by
  let f : ℕ → ℝ := fun n => 1/(n:ℝ)^2
  have heven : Summable (fun n : ℕ => f (2*n)) :=
    hB.summable.comp_injective (fun _ _ h => by omega)
  have hodd : Summable (fun n : ℕ => f (2*n+1)) :=
    hB.summable.comp_injective ((add_left_injective 1).comp
      (fun _ _ h => by omega))
  have hevenSum : (∑' n : ℕ, f (2*n)) = B/4 := by
    have h : HasSum (fun n : ℕ => f (2*n)) (B/4) := by
      convert! hB.div_const 4 using 1
      ext n
      simp only [f,Nat.cast_mul,Nat.cast_ofNat,mul_pow,mul_inv_rev,one_div]
      norm_num
      ring
    exact h.tsum_eq
  have hoddSum : (∑' n : ℕ, f (2*n+1)) = 3*B/4 := by
    have h := tsum_even_add_odd heven hodd
    rw [hevenSum,hB.tsum_eq] at h
    linarith
  have hpos : HasSum (fun n : ℕ => 1/((1/2:ℝ)+(n:ℝ))^2) (3*B) := by
    convert! hodd.hasSum.mul_left 4 using 1
    · ext n
      dsimp only [f]
      push_cast
      rw [show (1/2:ℝ)+(n:ℝ) = (2*(n:ℝ)+1)/2 by ring,div_pow,one_div_div]
      norm_num
      ring
    · rw [hoddSum]
      ring
  have hneg : HasSum (fun n : ℕ => 1/((1/2:ℝ)+((-(n+1):ℤ):ℝ))^2) (3*B) := by
    convert! hpos using 1
    ext n
    push_cast
    rw [show (1/2:ℝ)+(-((n:ℝ)+1)) = -((1/2:ℝ)+(n:ℝ)) by ring,neg_sq]
  have htail : HasSum (fun n : ℕ => 1/((n+1:ℕ):ℝ)^2) B := by
    have h := (hasSum_nat_add_iff' 1).mpr hB
    simpa using h
  have hneg0 : HasSum (fun n : ℕ => 1/((-(n+1):ℤ):ℝ)^2) B := by
    convert! htail using 1
    ext n
    push_cast
    rw [neg_sq]
  constructor
  · have h : HasSum (fun m : ℤ => 1/((1/2:ℝ)+(m:ℝ))^2) (3*B+3*B) :=
      HasSum.of_nat_of_neg_add_one
        (f := fun m : ℤ => 1/((1/2:ℝ)+(m:ℝ))^2)
        (by simpa only [Int.cast_natCast] using hpos) hneg
    convert! h using 1
    ring
  · have h : HasSum (fun m : ℤ => 1/(m:ℝ)^2) (B+B) :=
      HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => 1/(m:ℝ)^2)
        (by simpa only [Int.cast_natCast] using hB) hneg0
    convert! h using 1
    ring

private theorem real_half_integer_row (B : ℝ)
    (hB : HasSum (fun n : ℕ => 1/(n:ℝ)^2) B) :
    HasSum (fun m : ℤ => (1/((1/2:ℂ)-(m:ℂ))^2-1/(m:ℂ)^2))
      (Complex.ofReal (4*B)) := by
  obtain ⟨hhalf,hzero⟩ := inverse_square_integer_rows B hB
  have h := hhalf.sub hzero
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr h
  have hR : HasSum (fun m : ℤ => (1/((1/2:ℝ)-(m:ℝ))^2-1/(m:ℝ)^2)) (4*B) := by
    convert! hneg using 1
    · funext m
      dsimp only [Function.comp_def]
      simp only [Equiv.neg_apply,Int.cast_neg,neg_sq]
      ring
    · ring
  convert! Complex.hasSum_ofReal.mpr hR using 1
  funext m
  push_cast
  ring

theorem integer_real_half_shift_difference :
    (∑' m : ℤ, (1/((1/2:ℂ)-(m:ℂ))^2-1/(m:ℂ)^2)) =
      Complex.ofReal (2*Real.pi^2/3) := by
  have h := real_half_integer_row (Real.pi^2/6) hasSum_zeta_two
  convert! h.tsum_eq using 1
  congr 1
  ring

end Lemniscate
