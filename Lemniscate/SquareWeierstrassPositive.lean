import Lemniscate.WeierstrassRows
import Lemniscate.WeierstrassProfile

/-! Positivity at the real half-period and existence of the real scaling. -/
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

private def realHalfSummand (m : ℤ) : ℝ :=
  1/((1/2:ℝ)-(m:ℝ))^2-1/(m:ℝ)^2

private theorem square_half_zero_cast (m : ℤ) :
    squareHalfSummand 0 m = (realHalfSummand m : ℂ) := by
  dsimp only [squareHalfSummand,realHalfSummand]
  push_cast
  simp only [zero_mul,add_zero]

private theorem inverse_square_pair_identity (h x : ℝ)
    (hx : x ≠ 0) (hm : h-x ≠ 0) (hp : h+x ≠ 0) (hq : x^2-h^2 ≠ 0) :
    1/(h-x)^2+1/(h+x)^2-2/x^2 =
      2*h^2*(3*x^2-h^2)/(x^2*(x^2-h^2)^2) := by
  field_simp
  ring

private theorem real_half_pairs_nonneg (m : ℤ) :
    0 ≤ realHalfSummand m+realHalfSummand (-m) := by
  by_cases hm : m = 0
  · subst m
    norm_num [realHalfSummand]
  have hm2 : (1:ℝ) ≤ (m:ℝ)^2 := by
    have hcases : m ≤ -1 ∨ 1 ≤ m := by omega
    rcases hcases with h | h
    · have h' : (m:ℝ) ≤ -1 := by exact_mod_cast h
      nlinarith [sq_nonneg ((m:ℝ)+1)]
    · have h' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast h
      nlinarith [sq_nonneg ((m:ℝ)-1)]
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  have hmminus : (1/2:ℝ)-(m:ℝ) ≠ 0 := by intro h; nlinarith
  have hmplus : (1/2:ℝ)+(m:ℝ) ≠ 0 := by intro h; nlinarith
  have hmq : (m:ℝ)^2-(1/4:ℝ) ≠ 0 := by linarith
  have hid : realHalfSummand m+realHalfSummand (-m) =
      2*(1/2:ℝ)^2*(3*(m:ℝ)^2-(1/2:ℝ)^2)/
        ((m:ℝ)^2*((m:ℝ)^2-(1/2:ℝ)^2)^2) := by
    dsimp only [realHalfSummand]
    rw [Int.cast_neg,sub_neg_eq_add,neg_sq]
    calc
      _ = 1/((1/2:ℝ)-m)^2+1/((1/2:ℝ)+m)^2-2/(m:ℝ)^2 := by ring
      _ = 2*(1/2:ℝ)^2*(3*(m:ℝ)^2-(1/2:ℝ)^2)/
          ((m:ℝ)^2*((m:ℝ)^2-(1/2:ℝ)^2)^2) :=
        inverse_square_pair_identity (1/2) m hmR hmminus hmplus (by norm_num; exact hmq)
  rw [hid]
  exact div_nonneg (mul_nonneg (by positivity) (by nlinarith)) (by positivity)

private theorem square_half_zero_positive :
    (∑' m : ℤ, squareHalfSummand 0 m).im = 0 ∧
      4 ≤ (∑' m : ℤ, squareHalfSummand 0 m).re := by
  have hs := square_half_hasSum.summable.prod_factor (0:ℤ)
  have hg : Summable realHalfSummand := by
    convert! (Complex.hasSum_re hs.hasSum).summable using 1
    ext m
    rw [square_half_zero_cast]
    rfl
  have hn : Summable (fun m : ℤ => realHalfSummand (-m)) :=
    hg.comp_injective (Equiv.neg ℤ).injective
  have hneg : (∑' m : ℤ, realHalfSummand (-m)) = ∑' m : ℤ, realHalfSummand m := by
    simpa only [Equiv.neg_apply] using (Equiv.neg ℤ).tsum_eq realHalfSummand
  have he : (∑' m : ℤ, (realHalfSummand m+realHalfSummand (-m))) =
      2*(∑' m : ℤ, realHalfSummand m) := by
    rw [hg.tsum_add hn,hneg]
    ring
  have hbound := (hg.add hn).le_tsum (0:ℤ) (fun m _ => real_half_pairs_nonneg m)
  rw [he] at hbound
  have hzero : realHalfSummand 0+realHalfSummand (-0) = 8 := by
    norm_num [realHalfSummand]
  rw [hzero] at hbound
  have hrow : (∑' m : ℤ, squareHalfSummand 0 m) =
      Complex.ofReal (∑' m : ℤ, realHalfSummand m) := by
    calc
      _ = ∑' m : ℤ, (realHalfSummand m:ℂ) := tsum_congr square_half_zero_cast
      _ = _ := (Complex.ofReal_tsum realHalfSummand).symm
  rw [hrow]
  exact ⟨rfl,by simpa only [Complex.ofReal_re] using (show
    4 ≤ ∑' m : ℤ, realHalfSummand m by linarith)⟩

private theorem square_half_positive_row (n : ℤ) (hn : 0 < n) :
    ∃ r : ℝ, 0 ≤ r ∧ (∑' m : ℤ, squareHalfSummand n m) = (r:ℂ) := by
  let r : ℝ :=
    4*Real.pi^2*Real.exp (-2*Real.pi*n)/(1+Real.exp (-2*Real.pi*n))^2 +
      4*Real.pi^2*Real.exp (-2*Real.pi*n)/(1-Real.exp (-2*Real.pi*n))^2
  refine ⟨r,by dsimp only [r]; positivity,?_⟩
  rw [square_half_row,integerSquareSum_half_reflect]
  have h := integer_half_shift_difference (n:ℝ) (by exact_mod_cast hn)
  change integerSquareSum (1/2+I*((n:ℝ):ℂ)) -
    integerSquareSum (I*((n:ℝ):ℂ)) = (r:ℂ) at h
  simpa only [Complex.ofReal_intCast,mul_comm I] using h

theorem unit_square_normalization_exists :
    ∃ a : ℝ, 0 < a ∧ 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1 := by
  have hrows := square_half_hasSum.prod_fiberwise
    (fun n => (square_half_hasSum.summable.prod_factor n).hasSum)
  have hre := Complex.hasSum_re hrows
  have him := Complex.hasSum_im hrows
  have hnonneg (n : ℤ) : (∑' m : ℤ, squareHalfSummand n m).im = 0 ∧
      0 ≤ (∑' m : ℤ, squareHalfSummand n m).re := by
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · obtain ⟨r,hr,he⟩ := square_half_positive_row (-n) (by omega)
      rw [square_half_row_neg n] at he
      rw [he]
      exact ⟨rfl,hr⟩
    · exact ⟨square_half_zero_positive.1,le_trans (by norm_num) square_half_zero_positive.2⟩
    · obtain ⟨r,hr,he⟩ := square_half_positive_row n hn
      rw [he]
      exact ⟨rfl,hr⟩
  have hbound : 4 ≤ (unitSquarePeriods.weierstrassP (1/2)).re := by
    calc
      4 ≤ (∑' m : ℤ, squareHalfSummand 0 m).re := square_half_zero_positive.2
      _ ≤ ∑' n : ℤ, (∑' m : ℤ, squareHalfSummand n m).re :=
        hre.summable.le_tsum 0 (fun n _ => (hnonneg n).2)
      _ = _ := hre.tsum_eq
  have himzero : (unitSquarePeriods.weierstrassP (1/2)).im = 0 := by
    rw [← him.tsum_eq]
    calc
      _ = ∑' _ : ℤ, (0:ℝ) := tsum_congr (fun n => (hnonneg n).1)
      _ = 0 := tsum_zero
  let E : ℝ := (unitSquarePeriods.weierstrassP (1/2)).re
  have hE : 0 < E := by dsimp only [E]; linarith
  have hreal : unitSquarePeriods.weierstrassP (1/2) = (E:ℂ) := by
    apply Complex.ext
    · rfl
    · exact himzero
  let a := Real.sqrt (1/(2*E))
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a^2 = 1/(2*E) := Real.sq_sqrt (by positivity)
  have hR : 2*a^2*E = 1 := by
    rw [ha2]
    field_simp
  refine ⟨a,ha,?_⟩
  rw [hreal]
  exact_mod_cast hR

end Lemniscate
