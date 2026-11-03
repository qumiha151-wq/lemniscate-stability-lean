import Lemniscate.WeierstrassFourierRows
import Lemniscate.WeierstrassFrequencyBounds
import Lemniscate.WeierstrassZeroRow
import Lemniscate.WeierstrassProfile

/-! The exact square-lattice half-period series, real normalization and squared frequency. -/
noncomputable section
namespace Lemniscate
open Complex

private theorem integerSquareSum_half_reflect (z : ℂ) :
    weierstrassIntegerRow (1/2-z) = weierstrassIntegerRow (1/2+z) := by
  calc
    weierstrassIntegerRow (1/2-z) = weierstrassIntegerRow (-(1/2-z)) :=
      (weierstrass_integer_row_neg _).symm
    _ = weierstrassIntegerRow ((1/2+z)-1) := by congr 1; ring
    _ = weierstrassIntegerRow (1/2+z) := by
      simpa only [sub_add_cancel] using (weierstrass_integer_row_add_one ((1/2+z)-1)).symm

private def squareHalfSummand (n m : ℤ) : ℂ :=
  1/((1/2:ℂ)-((m:ℂ)+(n:ℂ)*I))^2 - 1/((m:ℂ)+(n:ℂ)*I)^2

private theorem square_half_hasSum :
    HasSum (fun p : ℤ×ℤ => squareHalfSummand p.1 p.2)
      (unitSquarePeriods.weierstrassP (1/2)) := by
  simpa only [squareHalfSummand,zero_sub,neg_sq,
    unitSquarePeriods.weierstrassP_zero,sub_zero] using
      unit_square_weierstrass_difference_hasSum (1/2) 0

private theorem square_half_row (n : ℤ) :
    (∑' m : ℤ, squareHalfSummand n m) =
      weierstrassIntegerRow (1/2-(n:ℂ)*I) - weierstrassIntegerRow ((n:ℂ)*I) := by
  simpa only [squareHalfSummand,zero_sub,neg_sq,weierstrass_integer_row_neg] using
    weierstrass_difference_row (1/2) 0 n

private theorem square_half_row_neg (n : ℤ) :
    (∑' m : ℤ, squareHalfSummand (-n) m) =
      (∑' m : ℤ, squareHalfSummand n m) := by
  rw [square_half_row,square_half_row]
  simp only [Int.cast_neg,neg_mul]
  rw [sub_neg_eq_add,
    integerSquareSum_half_reflect,weierstrass_integer_row_neg]

private theorem square_half_positive_row (n : ℕ) :
    (∑' m : ℤ, squareHalfSummand ((n+1:ℕ):ℤ) m) =
      Complex.ofReal (4*Real.pi^2*weierstrassHalfPeriodTerm (Real.exp (-Real.pi)) n) := by
  rw [square_half_row,integerSquareSum_half_reflect]
  have h := integer_half_shift_difference ((n+1:ℕ):ℝ) (by positivity)
  have hexp : Real.exp (-2*Real.pi*((n+1:ℕ):ℝ)) =
      Real.exp (-Real.pi)^(2*(n+1)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hvalue :
      4*Real.pi^2*Real.exp (-2*Real.pi*((n+1:ℕ):ℝ))/
          (1+Real.exp (-2*Real.pi*((n+1:ℕ):ℝ)))^2 +
        4*Real.pi^2*Real.exp (-2*Real.pi*((n+1:ℕ):ℝ))/
          (1-Real.exp (-2*Real.pi*((n+1:ℕ):ℝ)))^2 =
      4*Real.pi^2*weierstrassHalfPeriodTerm (Real.exp (-Real.pi)) n := by
    rw [hexp]
    dsimp only [weierstrassHalfPeriodTerm]
    ring
  rw [hvalue] at h
  change weierstrassIntegerRow (1/2+I*(((n+1:ℕ):ℝ):ℂ)) -
    weierstrassIntegerRow (I*(((n+1:ℕ):ℝ):ℂ)) = _ at h
  simpa only [Int.cast_natCast,Complex.ofReal_natCast,mul_comm I] using h

theorem unit_square_half_period_series :
    unitSquarePeriods.weierstrassP (1/2) =
        Complex.ofReal ((2*Real.pi^2/3)*
          (1+12*(∑' n : ℕ, weierstrassHalfPeriodTerm (Real.exp (-Real.pi)) n))) := by
  let R : ℤ → ℂ := fun n => ∑' m : ℤ, squareHalfSummand n m
  let t := weierstrassHalfPeriodTerm (Real.exp (-Real.pi))
  have hrows : HasSum R (unitSquarePeriods.weierstrassP (1/2)) :=
    square_half_hasSum.prod_fiberwise
      (fun n => (square_half_hasSum.summable.prod_factor n).hasSum)
  have hsNat : Summable (fun n : ℕ => R (n:ℤ)) :=
    hrows.summable.comp_injective (fun _ _ h => by exact_mod_cast h)
  have hsTail : Summable (fun n : ℕ => R ((n:ℤ)+1)) := by
    simpa only [Int.natCast_add,Int.natCast_one] using
      (summable_nat_add_iff 1).mpr hsNat
  have heven (n : ℤ) : R (-n) = R n := square_half_row_neg n
  have hsNeg : Summable (fun n : ℕ => R (-((n:ℤ)+1))) := by
    simpa only [heven] using hsTail
  have hrow (n : ℕ) : R ((n:ℤ)+1) = Complex.ofReal (4*Real.pi^2*t n) := by
    simpa only [Int.natCast_add,Int.natCast_one] using square_half_positive_row n
  have hzero : R 0 = Complex.ofReal (2*Real.pi^2/3) := by
    simpa only [R,squareHalfSummand,Int.cast_zero,zero_mul,add_zero] using
      integer_real_half_shift_difference
  have hnat : (∑' n : ℕ, R (n:ℤ)) = R 0+(∑' n : ℕ, R ((n:ℤ)+1)) := by
    simpa only [Int.natCast_zero,Int.natCast_add,Int.natCast_one] using hsNat.tsum_eq_zero_add
  have hsplit : unitSquarePeriods.weierstrassP (1/2) =
      R 0+2*(∑' n : ℕ, R ((n:ℤ)+1)) := by
    calc
      _ = ∑' n : ℤ, R n := hrows.tsum_eq.symm
      _ = _ := by
        rw [tsum_of_nat_of_neg_add_one (f := R) hsNat hsNeg,hnat]
        simp only [heven]
        ring
  have htailvalue : (∑' n : ℕ, R ((n:ℤ)+1)) =
      Complex.ofReal (4*Real.pi^2*(∑' n : ℕ, t n)) := by
    calc
      _ = ∑' n : ℕ, Complex.ofReal (4*Real.pi^2*t n) := tsum_congr hrow
      _ = Complex.ofReal (∑' n : ℕ, 4*Real.pi^2*t n) := (Complex.ofReal_tsum _).symm
      _ = _ := by rw [tsum_mul_left]
  rw [hsplit,hzero,htailvalue]
  push_cast
  ring

theorem unit_square_normalization_exists :
    ∃ a : ℝ, 0 < a ∧ 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1 := by
  have hvalue := unit_square_half_period_series
  let S := ∑' n : ℕ, weierstrassHalfPeriodTerm (Real.exp (-Real.pi)) n
  have hS : 0 ≤ S := tsum_nonneg (fun n => by dsimp only [weierstrassHalfPeriodTerm]; positivity)
  let E : ℝ := (2*Real.pi^2/3)*(1+12*S)
  have hE : 0 < E := by dsimp only [E]; positivity
  have hreal : unitSquarePeriods.weierstrassP (1/2) = (E:ℂ) := hvalue
  let a := Real.sqrt (1/(2*E))
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a^2 = 1/(2*E) := Real.sq_sqrt (by positivity)
  have hR : 2*a^2*E = 1 := by
    rw [ha2]
    field_simp
  refine ⟨a,ha,?_⟩
  rw [hreal]
  exact_mod_cast hR

theorem square_weierstrass_frequency_squared (a : ℝ)
    (hnorm : 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1) :
    (Real.pi*a)^2 = 3/(4*(1+12*(∑' n : ℕ,
      weierstrassHalfPeriodTerm (Real.exp (-Real.pi)) n))) := by
  have hvalue := unit_square_half_period_series
  let S := ∑' n : ℕ, weierstrassHalfPeriodTerm (Real.exp (-Real.pi)) n
  have hS : 0 ≤ S := tsum_nonneg (fun n => by dsimp only [weierstrassHalfPeriodTerm]; positivity)
  rw [hvalue] at hnorm
  have hR : 2*a^2*((2*Real.pi^2/3)*(1+12*S)) = 1 := by exact_mod_cast hnorm
  have hd : 4*(1+12*S) ≠ 0 := by positivity
  apply (eq_div_iff hd).mpr
  linear_combination (3:ℝ)*hR

end Lemniscate
