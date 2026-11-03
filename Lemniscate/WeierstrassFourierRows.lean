import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Lemniscate.WeierstrassRows
import Lemniscate.WeierstrassProfile

/-! Convergent Fourier rows for the centered square-lattice Weierstrass function. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped UpperHalfPlane

theorem integer_inverse_square_fourier (z : ℂ) (hz : 0 < z.im) :
    HasSum (fun n : ℕ => -4*(Real.pi:ℂ)^2*((n+1:ℕ):ℂ)*
      Complex.exp (2*Real.pi*I*z)^(n+1))
      (∑' m : ℤ, 1/(z+m)^2) := by
  let E := Complex.exp (2*Real.pi*I*z)
  have hE : ‖E‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z,hz⟩
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hE).mul_left
    (-4*(Real.pi:ℂ)^2)
  have hs := (hasSum_nat_add_iff' 1).mpr h
  rw [integer_inverse_square_sum z hz]
  simpa only [E,Finset.sum_range_one,Nat.cast_zero,zero_mul,mul_zero,
    sub_zero,mul_assoc,div_eq_mul_inv] using hs

theorem unit_square_weierstrass_difference_hasSum (z w : ℂ) :
    HasSum (fun p : ℤ×ℤ =>
      1/(z-((p.2:ℂ)+(p.1:ℂ)*I))^2-
      1/(w-((p.2:ℂ)+(p.1:ℂ)*I))^2)
      (unitSquarePeriods.weierstrassP z-unitSquarePeriods.weierstrassP w) := by
  let L := unitSquarePeriods
  let e : (ℤ×ℤ) ≃ L.lattice :=
    (Equiv.prodComm ℤ ℤ).trans L.latticeEquivProd.toEquiv.symm
  have he (p : ℤ×ℤ) : (e p : ℂ) = (p.2:ℂ)+(p.1:ℂ)*I := by
    change ((L.latticeEquivProd.symm (p.2,p.1)):ℂ) = _
    rw [L.latticeEquiv_symm_apply]
    change (p.2:ℂ)*1+(p.1:ℂ)*I = _
    rw [mul_one]
  have h := e.hasSum_iff.mpr ((L.hasSum_weierstrassP z).sub
    (L.hasSum_weierstrassP w))
  convert! h using 1
  funext p
  dsimp only [Function.comp_def]
  rw [he]
  ring

def weierstrassIntegerRow (z : ℂ) : ℂ := ∑' m : ℤ, 1/(z+m)^2

theorem weierstrass_integer_row_add_one (z : ℂ) :
    weierstrassIntegerRow (z+1) = weierstrassIntegerRow z := by
  dsimp only [weierstrassIntegerRow]
  conv_rhs => rw [← (Equiv.addRight (1:ℤ)).tsum_eq (fun m : ℤ => 1/(z+m)^2)]
  apply tsum_congr
  intro m
  simp only [Equiv.coe_addRight,Int.cast_add,Int.cast_one]
  ring

private theorem integer_row_summable (z : ℂ) :
    Summable (fun m : ℤ => 1/(z+m)^2) := by
  simpa only [Int.cast_one,one_mul,zpow_ofNat,one_div] using
    EisensteinSeries.linear_right_summable z 1 (k := 2) (by norm_num)

theorem weierstrass_difference_row (z w : ℂ) (n : ℤ) :
    (∑' m : ℤ, (1/(z-((m:ℂ)+(n:ℂ)*I))^2-
      1/(w-((m:ℂ)+(n:ℂ)*I))^2)) =
      weierstrassIntegerRow (z-(n:ℂ)*I)-weierstrassIntegerRow (w-(n:ℂ)*I) := by
  have hs (v : ℂ) : Summable (fun m : ℤ => 1/(v-((m:ℂ)+(n:ℂ)*I))^2) := by
    have h := (integer_row_summable (v-(n:ℂ)*I)).comp_injective (Equiv.neg ℤ).injective
    convert! h using 1
    funext m
    simp only [Function.comp_def,Equiv.neg_apply,Int.cast_neg]
    ring
  have he (v : ℂ) : (∑' m : ℤ, 1/(v-((m:ℂ)+(n:ℂ)*I))^2) =
      weierstrassIntegerRow (v-(n:ℂ)*I) := by
    dsimp only [weierstrassIntegerRow]
    conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq
      (fun m : ℤ => 1/(v-((m:ℂ)+(n:ℂ)*I))^2)]
    apply tsum_congr
    intro m
    simp only [Equiv.neg_apply,Int.cast_neg]
    ring
  rw [(hs z).tsum_sub (hs w),he z,he w]

theorem unit_square_weierstrass_difference_rows (z w : ℂ) :
    HasSum (fun n : ℤ => weierstrassIntegerRow (z-(n:ℂ)*I)-weierstrassIntegerRow (w-(n:ℂ)*I))
      (unitSquarePeriods.weierstrassP z-unitSquarePeriods.weierstrassP w) := by
  have h := unit_square_weierstrass_difference_hasSum z w
  have hr := h.prod_fiberwise (fun n => (h.summable.prod_factor n).hasSum)
  convert! hr using 1
  funext n
  exact (weierstrass_difference_row z w n).symm

theorem weierstrass_integer_row_neg (z : ℂ) : weierstrassIntegerRow (-z) = weierstrassIntegerRow z := by
  dsimp only [weierstrassIntegerRow]
  conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ => 1/(-z+m)^2)]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply,Int.cast_neg]
  rw [show -z+(-(m:ℂ)) = -(z+m) by ring,neg_sq]

theorem unit_square_centered_paired_rows (x : ℝ) :
    HasSum (fun k : ℕ => weierstrassIntegerRow ((x:ℂ)+((k:ℂ)+1/2)*I)+
      weierstrassIntegerRow (-(x:ℂ)+((k:ℂ)+1/2)*I)-2*weierstrassIntegerRow (((k:ℂ)+1/2)*I))
      (unitSquarePeriods.weierstrassP ((x:ℂ)+I/2)-
        unitSquarePeriods.weierstrassP (I/2)) := by
  let R : ℤ → ℂ := fun n =>
    weierstrassIntegerRow ((x:ℂ)+I/2-(n:ℂ)*I)-weierstrassIntegerRow (I/2-(n:ℂ)*I)
  let F : ℤ → ℂ := fun n => R (-n)
  have hr : HasSum F (unitSquarePeriods.weierstrassP ((x:ℂ)+I/2)-
      unitSquarePeriods.weierstrassP (I/2)) :=
    (Equiv.neg ℤ).hasSum_iff.mpr (unit_square_weierstrass_difference_rows _ _)
  have hnat : Summable (fun k : ℕ => F (k:ℤ)) :=
    hr.summable.comp_injective (fun _ _ h => by exact_mod_cast h)
  have hneg : Summable (fun k : ℕ => F (-((k:ℤ)+1))) :=
    hr.summable.comp_injective (fun _ _ h => by omega)
  have hpair : HasSum (fun k : ℕ => F (k:ℤ)+F (-((k:ℤ)+1)))
      (unitSquarePeriods.weierstrassP ((x:ℂ)+I/2)-
        unitSquarePeriods.weierstrassP (I/2)) := by
    rw [← hr.tsum_eq,tsum_of_nat_of_neg_add_one (f := F) hnat hneg]
    exact hnat.hasSum.add hneg.hasSum
  convert! hpair using 1
  funext k
  dsimp only [F,R]
  simp only [Int.cast_neg,Int.cast_add,Int.cast_one,Int.cast_natCast,neg_neg]
  rw [show (x:ℂ)+I/2-(-(k:ℂ))*I = (x:ℂ)+((k:ℂ)+1/2)*I by ring,
    show I/2-(-(k:ℂ))*I = ((k:ℂ)+1/2)*I by ring,
    show (x:ℂ)+I/2-((k:ℂ)+1)*I = -(-(x:ℂ)+((k:ℂ)+1/2)*I) by ring,
    show I/2-((k:ℂ)+1)*I = -(((k:ℂ)+1/2)*I) by ring,
    weierstrass_integer_row_neg,weierstrass_integer_row_neg]
  ring

theorem integer_half_height_row_fourier (x : ℝ) (k : ℕ) :
    HasSum (fun n : ℕ => -4*(Real.pi:ℂ)^2*((n+1:ℕ):ℂ)*
      (Real.exp (-Real.pi):ℂ)^((2*k+1)*(n+1))*
      (Complex.exp (2*Real.pi*I*(x:ℂ)))^(n+1))
      (weierstrassIntegerRow ((x:ℂ)+((k:ℂ)+1/2)*I)) := by
  have hz : 0 < ((x:ℂ)+((k:ℂ)+1/2)*I).im := by
    norm_num
    positivity
  have he : Complex.exp (2*Real.pi*I*((x:ℂ)+((k:ℂ)+1/2)*I)) =
      (Real.exp (-Real.pi):ℂ)^(2*k+1)*Complex.exp (2*Real.pi*I*(x:ℂ)) := by
    rw [Complex.ofReal_exp,← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  have h := integer_inverse_square_fourier _ hz
  change HasSum _ (weierstrassIntegerRow _) at h
  rw [he] at h
  convert! h using 1
  funext n
  rw [mul_pow,← pow_mul]
  ring

theorem centered_half_height_row_fourier (x : ℝ) (k : ℕ) :
    HasSum (fun n : ℕ => -4*(Real.pi:ℂ)^2*((n+1:ℕ):ℂ)*
      (Real.exp (-Real.pi):ℂ)^((2*k+1)*(n+1))*
      ((Complex.exp (2*Real.pi*I*(x:ℂ)))^(n+1)+
        (Complex.exp (2*Real.pi*I*(-(x:ℂ))))^(n+1)-2))
      (weierstrassIntegerRow ((x:ℂ)+((k:ℂ)+1/2)*I)+
        weierstrassIntegerRow (-(x:ℂ)+((k:ℂ)+1/2)*I)-2*weierstrassIntegerRow (((k:ℂ)+1/2)*I)) := by
  have h := ((integer_half_height_row_fourier x k).add
    (integer_half_height_row_fourier (-x) k)).sub
      ((integer_half_height_row_fourier 0 k).mul_left 2)
  convert! h using 1
  · funext n
    simp only [Complex.ofReal_neg,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_pow]
    ring
  · simp only [Complex.ofReal_neg,Complex.ofReal_zero,zero_add]

private def centeredFourierPhase (x : ℝ) (n : ℕ) : ℂ :=
  (Complex.exp (2*Real.pi*I*(x:ℂ)))^(n+1)+
    (Complex.exp (2*Real.pi*I*(-(x:ℂ))))^(n+1)-2

private theorem centered_fourier_phase_bound (x : ℝ) (n : ℕ) :
    ‖centeredFourierPhase x n‖ ≤ 4 := by
  have hnorm (y : ℝ) : ‖Complex.exp (2*Real.pi*I*(y:ℂ))‖ = 1 := by
    simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  dsimp only [centeredFourierPhase]
  calc
    _ ≤ ‖(Complex.exp (2*Real.pi*I*(x:ℂ)))^(n+1)+
      (Complex.exp (2*Real.pi*I*(-(x:ℂ))))^(n+1)‖+‖(2:ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖(Complex.exp (2*Real.pi*I*(x:ℂ)))^(n+1)‖+
      ‖(Complex.exp (2*Real.pi*I*(-(x:ℂ))))^(n+1)‖)+‖(2:ℂ)‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ = 4 := by
      rw [norm_pow,norm_pow,hnorm x]
      simpa only [Complex.ofReal_neg] using
        (show (1:ℝ)^(n+1)+‖Complex.exp (2*Real.pi*I*((-x:ℝ):ℂ))‖^(n+1)+
          ‖(2:ℂ)‖ = 4 by rw [hnorm (-x)]; norm_num)

private theorem summable_half_period_weights (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun p : ℕ×ℕ => ((p.2+1:ℕ):ℝ)*q^((2*p.1+1)*(p.2+1))) := by
  have hqn : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hq] using hq1
  have hj : Summable (fun n : ℕ => ((n+1:ℕ):ℝ)*q^(n+1)) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hqn).summable.comp_injective
      (fun _ _ h => by omega)
  have hk : Summable (fun k : ℕ => (q^2)^k) :=
    summable_geometric_of_lt_one (sq_nonneg q) (pow_lt_one₀ hq hq1 (by decide))
  have hp := hk.mul_of_nonneg hj (fun _ => by positivity) (fun _ => by positivity)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) ?_ hp
  rintro ⟨k,n⟩
  calc
    ((n+1:ℕ):ℝ)*q^((2*k+1)*(n+1)) ≤
        ((n+1:ℕ):ℝ)*q^(2*k+(n+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_of_le_one hq hq1.le (by nlinarith)
    _ = (q^2)^k*(((n+1:ℕ):ℝ)*q^(n+1)) := by rw [pow_add,pow_mul]; ring

theorem summable_half_period_fourier_double (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (b : ℕ → ℂ) (K : ℝ) (hb : ∀ n, ‖b n‖ ≤ K) :
    Summable (fun p : ℕ×ℕ =>
      ‖((p.2+1:ℕ):ℂ)*(q:ℂ)^((2*p.1+1)*(p.2+1))*b p.2‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    ((summable_half_period_weights q hq hq1).mul_right K)
  intro p
  rw [norm_mul,norm_mul,Complex.norm_natCast,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hq]
  exact mul_le_mul_of_nonneg_left (hb p.2) (by positivity)

theorem half_period_geometric_hasSum (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) :
    HasSum (fun k : ℕ => q^((2*k+1)*j)) (q^j/(1-q^(2*j))) := by
  have hpow : ‖q^(2*j)‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq _)]
    exact pow_lt_one₀ hq hq1 (by omega)
  convert! (hasSum_geometric_of_norm_lt_one hpow).mul_left (q^j) using 1
  · funext k
    rw [← pow_mul,← pow_add]
    congr 1
    ring


theorem unit_square_weierstrass_fourier (x : ℝ) :
    HasSum (fun n : ℕ => -4*(Real.pi:ℂ)^2*((n+1:ℕ):ℂ)*
      (Real.exp (-Real.pi):ℂ)^(n+1)/
        (1-(Real.exp (-Real.pi):ℂ)^(2*(n+1)))*
      ((Complex.exp (2*Real.pi*I*(x:ℂ)))^(n+1)+
        (Complex.exp (2*Real.pi*I*(-(x:ℂ))))^(n+1)-2))
      (unitSquarePeriods.weierstrassP ((x:ℂ)+I/2)-
        unitSquarePeriods.weierstrassP (I/2)) := by
  let q : ℝ := Real.exp (-Real.pi)
  let C : ℂ := -4*(Real.pi:ℂ)^2
  let F : ℕ×ℕ → ℂ := fun p => C*((p.2+1:ℕ):ℂ)*
    (q:ℂ)^((2*p.1+1)*(p.2+1))*centeredFourierPhase x p.2
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp only [q]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos)
  have hd0 := (summable_half_period_fourier_double q hq0 hq1
    (centeredFourierPhase x) 4 (centered_fourier_phase_bound x)).of_norm
  have hd : Summable F := by
    convert! hd0.mul_left C using 1
    funext p
    dsimp only [F]
    ring
  have hr (k : ℕ) : HasSum (fun n : ℕ => F (k,n))
      (weierstrassIntegerRow ((x:ℂ)+((k:ℂ)+1/2)*I)+
        weierstrassIntegerRow (-(x:ℂ)+((k:ℂ)+1/2)*I)-2*weierstrassIntegerRow (((k:ℂ)+1/2)*I)) := by
    exact centered_half_height_row_fourier x k
  have hvalue : (∑' p, F p) =
      unitSquarePeriods.weierstrassP ((x:ℂ)+I/2)-unitSquarePeriods.weierstrassP (I/2) :=
    (hd.hasSum.prod_fiberwise hr).unique (unit_square_centered_paired_rows x)
  have hc (n : ℕ) : HasSum (fun k : ℕ => F (k,n))
      (C*((n+1:ℕ):ℂ)*(q:ℂ)^(n+1)/(1-(q:ℂ)^(2*(n+1)))*
        centeredFourierPhase x n) := by
    have hg := Complex.hasSum_ofReal.mpr
      (half_period_geometric_hasSum q hq0 hq1 (n+1) (by omega))
    have h := (hg.mul_left (C*((n+1:ℕ):ℂ))).mul_right (centeredFourierPhase x n)
    convert! h using 1
    · funext k
      dsimp only [F]
      push_cast
      ring
    · push_cast
      ring
  have h := hd.prod_symm.hasSum.prod_fiberwise hc
  have hswap : (∑' p : ℕ×ℕ, F p.swap) = ∑' p, F p :=
    (Equiv.prodComm ℕ ℕ).tsum_eq F
  rw [hswap,hvalue] at h
  exact h

theorem normalized_weierstrass_fourier (a : ℝ)
    (hnorm : 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1) (x : ℝ) :
    HasSum (fun n : ℕ => 8*((Real.pi*a)^2:ℝ)*((n+1:ℕ):ℂ)*
      (Real.exp (-Real.pi):ℂ)^(n+1)/
        (1-(Real.exp (-Real.pi):ℂ)^(2*(n+1)))*
      ((Complex.exp (2*Real.pi*I*((a*x:ℝ):ℂ)))^(n+1)+
        (Complex.exp (2*Real.pi*I*(-((a*x:ℝ):ℂ))))^(n+1)-2))
      (normalizedWeierstrass a x-1) := by
  have h0 := (normalized_weierstrass_data a hnorm).1
  have h := (unit_square_weierstrass_fourier (a*x)).mul_left (-2*(a:ℂ)^2)
  convert! h using 1
  · funext n
    push_cast
    ring
  · rw [← h0]
    dsimp only [normalizedWeierstrass]
    simp only [Complex.ofReal_mul,Complex.ofReal_zero,mul_zero,zero_add]
    ring

end Lemniscate
