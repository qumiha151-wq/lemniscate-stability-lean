import Lemniscate.WeierstrassZeroRow
import Lemniscate.WeierstrassProfile

/-! The exact square-lattice half-period series, real normalization and squared frequency. -/
noncomputable section
namespace Lemniscate
open Complex

private def integerSquareSum (z : ℂ) : ℂ := ∑' m : ℤ, 1/(z+m)^2

private theorem integerSquareSum_neg (z : ℂ) :
    integerSquareSum (-z) = integerSquareSum z := by
  dsimp only [integerSquareSum]
  conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ => 1/(-z+m)^2)]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply,Int.cast_neg]
  rw [show -z+(-(m:ℂ)) = -(z+m) by ring,neg_sq]

private theorem integerSquareSum_add_one (z : ℂ) :
    integerSquareSum (z+1) = integerSquareSum z := by
  dsimp only [integerSquareSum]
  conv_rhs => rw [← (Equiv.addRight (1:ℤ)).tsum_eq (fun m : ℤ => 1/(z+m)^2)]
  apply tsum_congr
  intro m
  simp only [Equiv.coe_addRight,Int.cast_add,Int.cast_one]
  ring

private theorem integerSquareSum_half_reflect (z : ℂ) :
    integerSquareSum (1/2-z) = integerSquareSum (1/2+z) := by
  calc
    integerSquareSum (1/2-z) = integerSquareSum (-(1/2-z)) :=
      (integerSquareSum_neg _).symm
    _ = integerSquareSum ((1/2+z)-1) := by congr 1; ring
    _ = integerSquareSum (1/2+z) := by
      simpa only [sub_add_cancel] using (integerSquareSum_add_one ((1/2+z)-1)).symm

private def squareHalfSummand (n m : ℤ) : ℂ :=
  1/((1/2:ℂ)-((m:ℂ)+(n:ℂ)*I))^2 - 1/((m:ℂ)+(n:ℂ)*I)^2

private theorem square_half_hasSum :
    HasSum (fun p : ℤ×ℤ => squareHalfSummand p.1 p.2)
      (unitSquarePeriods.weierstrassP (1/2)) := by
  let L := unitSquarePeriods
  let e : (ℤ×ℤ) ≃ L.lattice :=
    (Equiv.prodComm ℤ ℤ).trans L.latticeEquivProd.toEquiv.symm
  have he (p : ℤ×ℤ) : (e p : ℂ) = (p.2:ℂ)+(p.1:ℂ)*I := by
    change ((L.latticeEquivProd.symm (p.2,p.1)):ℂ) = _
    rw [L.latticeEquiv_symm_apply]
    change (p.2:ℂ)*1+(p.1:ℂ)*I = _
    rw [mul_one]
  have h := e.hasSum_iff.mpr (L.hasSum_weierstrassP (1/2))
  convert! h using 1
  funext p
  dsimp only [Function.comp_def]
  rw [he]
  rfl

private theorem square_half_row (n : ℤ) :
    (∑' m : ℤ, squareHalfSummand n m) =
      integerSquareSum (1/2-(n:ℂ)*I) - integerSquareSum ((n:ℂ)*I) := by
  have hsum (z : ℂ) : Summable (fun m : ℤ => 1/(z+m)^2) := by
    simpa only [Int.cast_one,one_mul,zpow_ofNat,one_div] using
      EisensteinSeries.linear_right_summable z 1 (k := 2) (by norm_num)
  have hfirst : (∑' m : ℤ, 1/((1/2:ℂ)-((m:ℂ)+(n:ℂ)*I))^2) =
      integerSquareSum (1/2-(n:ℂ)*I) := by
    dsimp only [integerSquareSum]
    conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq
      (fun m : ℤ => 1/((1/2:ℂ)-((m:ℂ)+(n:ℂ)*I))^2)]
    apply tsum_congr
    intro m
    simp only [Equiv.neg_apply,Int.cast_neg]
    ring
  have hsecond : (∑' m : ℤ, 1/((m:ℂ)+(n:ℂ)*I)^2) =
      integerSquareSum ((n:ℂ)*I) := by
    apply tsum_congr
    intro m
    rw [add_comm]
  have hsfirst : Summable (fun m : ℤ => 1/((1/2:ℂ)-((m:ℂ)+(n:ℂ)*I))^2) := by
    have hs := (hsum (1/2-(n:ℂ)*I)).comp_injective (Equiv.neg ℤ).injective
    convert! hs using 1
    ext m
    simp only [Function.comp_def,Equiv.neg_apply,Int.cast_neg]
    ring
  have hssecond : Summable (fun m : ℤ => 1/((m:ℂ)+(n:ℂ)*I)^2) := by
    simpa only [add_comm] using hsum ((n:ℂ)*I)
  change (∑' m : ℤ, (1/((1/2:ℂ)-((m:ℂ)+(n:ℂ)*I))^2 -
    1/((m:ℂ)+(n:ℂ)*I)^2)) = _
  rw [hsfirst.tsum_sub hssecond,hfirst,hsecond]

private theorem square_half_row_neg (n : ℤ) :
    (∑' m : ℤ, squareHalfSummand (-n) m) =
      (∑' m : ℤ, squareHalfSummand n m) := by
  rw [square_half_row,square_half_row]
  simp only [Int.cast_neg,neg_mul]
  rw [sub_neg_eq_add,
    integerSquareSum_half_reflect,integerSquareSum_neg]

def weierstrassHalfPeriodTerm (q : ℝ) (n : ℕ) : ℝ :=
  q^(2*(n+1))/(1+q^(2*(n+1)))^2 + q^(2*(n+1))/(1-q^(2*(n+1)))^2

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
  change integerSquareSum (1/2+I*(((n+1:ℕ):ℝ):ℂ)) -
    integerSquareSum (I*(((n+1:ℕ):ℝ):ℂ)) = _ at h
  simpa only [Int.cast_natCast,Complex.ofReal_natCast,mul_comm I] using h

theorem unit_square_half_period_series :
    Summable (weierstrassHalfPeriodTerm (Real.exp (-Real.pi))) ∧
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
  have hsValue : Summable (fun n : ℕ => 4*Real.pi^2*t n) := by
    convert! (Complex.hasSum_re hsTail.hasSum).summable using 1
    funext n
    rw [hrow]
    rfl
  have hpi : 4*Real.pi^2 ≠ 0 := by positivity
  have hsTerm : Summable t := by
    convert! hsValue.div_const (4*Real.pi^2) using 1
    funext n
    field_simp [hpi]
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
  refine ⟨hsTerm,?_⟩
  rw [hsplit,hzero,htailvalue]
  push_cast
  ring

theorem unit_square_normalization_exists :
    ∃ a : ℝ, 0 < a ∧ 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1 := by
  obtain ⟨_,hvalue⟩ := unit_square_half_period_series
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
  obtain ⟨_,hvalue⟩ := unit_square_half_period_series
  let S := ∑' n : ℕ, weierstrassHalfPeriodTerm (Real.exp (-Real.pi)) n
  have hS : 0 ≤ S := tsum_nonneg (fun n => by dsimp only [weierstrassHalfPeriodTerm]; positivity)
  rw [hvalue] at hnorm
  have hR : 2*a^2*((2*Real.pi^2/3)*(1+12*S)) = 1 := by exact_mod_cast hnorm
  have hd : 4*(1+12*S) ≠ 0 := by positivity
  apply (eq_div_iff hd).mpr
  linear_combination (3:ℝ)*hR

end Lemniscate
