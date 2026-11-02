import Lemniscate.PeriodicSymmetricCoefficient

/-! Coarse analytic estimates for the three symmetric coefficients. Square
weights avoid introducing square roots in the later Hilbert-Schmidt bound. -/
namespace Lemniscate

private theorem symmetric_scalar_absolute_bounds (r x y : ℝ) (hr : 0 ≤ r) :
    |evenSymmetricOffScalar r 0 x y| ≤
      r*(45*|x| * |y|+(15/4)*(|x|+|y|)^2) ∧
    |evenSymmetricOffScalar r 1 x y| ≤ 45*r*(|x|+|y|) ∧
    |evenSymmetricOffScalar r 2 x y| ≤ 45*r := by
  have hdiff : (x-y)^2 ≤ (|x|+|y|)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (x-y)) (abs_sub x y) 2
    norm_num only [sq_abs] at h
    exact h
  refine ⟨?_,?_,?_⟩
  · change |r*(45*x*y-(15/4)*(x-y)^2)| ≤ _
    rw [abs_mul,abs_of_nonneg hr]
    apply mul_le_mul_of_nonneg_left _ hr
    calc
      _ ≤ |45*x*y|+|(15/4:ℝ)*(x-y)^2| := abs_sub _ _
      _ = 45*|x| * |y|+(15/4)*(x-y)^2 := by
        norm_num [abs_mul,abs_of_nonneg (sq_nonneg (x-y))]
      _ ≤ _ := by linarith only [hdiff]
  · change |45*r*(x+y)| ≤ _
    rw [abs_mul,abs_mul,abs_of_nonneg hr]
    norm_num
    exact mul_le_mul_of_nonneg_left (abs_add_le x y) (by positivity)
  · change |45*r| ≤ _
    rw [abs_mul,abs_of_nonneg hr]
    norm_num

private theorem large_scalar_component_bounds (r x y : ℝ) (hr : 0 ≤ r) (hru : r ≤ 18/25)
    (hx : 24 ≤ |x|) (hy : 32 ≤ |y|) (j : Fin 3) :
    |evenSymmetricOffScalar r j x y| ≤ ![(3/50:ℝ),1/250,1/10000] j*x^2*y^2 := by
  have hx0 := abs_nonneg x
  have hy0 := abs_nonneg y
  have hx2 : (576:ℝ) ≤ x^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 24) hx 2
    norm_num only [sq_abs] at h
    exact h
  have hy2 : (1024:ℝ) ≤ y^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) hy 2
    norm_num only [sq_abs] at h
    exact h
  have hprod : (768:ℝ) ≤ |x| * |y| := by nlinarith only [mul_le_mul hx hy (by norm_num) hx0]
  have hprod2 : (|x| * |y|)^2 = x^2*y^2 := by rw [mul_pow,sq_abs,sq_abs]
  have hxy : |x| * |y| ≤ x^2*y^2/768 := by
    nlinarith only [hprod2,mul_nonneg (mul_nonneg hx0 hy0) (sub_nonneg.mpr hprod)]
  have hxx : x^2 ≤ x^2*y^2/1024 := by
    nlinarith only [mul_le_mul_of_nonneg_left hy2 (sq_nonneg x)]
  have hyy : y^2 ≤ x^2*y^2/576 := by
    nlinarith only [mul_le_mul_of_nonneg_left hx2 (sq_nonneg y)]
  have hax : |x| ≤ x^2/24 := by
    nlinarith only [sq_abs x,mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hay : |y| ≤ y^2/32 := by
    nlinarith only [sq_abs y,mul_nonneg hy0 (sub_nonneg.mpr hy)]
  have hxy2 : (589824:ℝ) ≤ x^2*y^2 := by
    nlinarith only [mul_le_mul hx2 hy2 (by norm_num) (sq_nonneg x)]
  have hs := symmetric_scalar_absolute_bounds r x y hr
  fin_cases j
  · change |evenSymmetricOffScalar r 0 x y| ≤ (3/50:ℝ)*x^2*y^2
    calc
      _ ≤ r*(45*|x| * |y|+(15/4)*(|x|+|y|)^2) := hs.1
      _ ≤ (18/25)*(45*|x| * |y|+(15/4)*(|x|+|y|)^2) := by gcongr
      _ ≤ _ := by nlinarith only [hxy,hxx,hyy,sq_abs x,sq_abs y]
  · change |evenSymmetricOffScalar r 1 x y| ≤ (1/250:ℝ)*x^2*y^2
    calc
      _ ≤ 45*r*(|x|+|y|) := hs.2.1
      _ ≤ 45*(18/25)*(|x|+|y|) := by gcongr
      _ ≤ _ := by nlinarith only [hax,hay,hxx,hyy]
  · change |evenSymmetricOffScalar r 2 x y| ≤ (1/10000:ℝ)*x^2*y^2
    exact hs.2.2.trans (by nlinarith only [hru,hxy2])

theorem even_symmetric_large_scalar_bound (r x y : ℝ) (hr : 0 ≤ r) (hru : r ≤ 18/25)
    (hx : 24 ≤ |x|) (hy : 32 ≤ |y|) :
    (∑ j : Fin 3, (evenSymmetricOffScalar r j x y)^2) ≤ (3/8)*(x^4/100)*y^4 := by
  calc
    _ ≤ ∑ j : Fin 3, (![(3/50:ℝ),1/250,1/10000] j*x^2*y^2)^2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := pow_le_pow_left₀ (abs_nonneg (evenSymmetricOffScalar r j x y))
        (large_scalar_component_bounds r x y hr hru hx hy j) 2
      simpa only [sq_abs] using h
    _ = (361601/100000000:ℝ)*x^4*y^4 := by
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val,
        Matrix.head_cons,Matrix.tail_cons,Fin.sum_univ_zero,add_zero]
      ring
    _ ≤ _ := by nlinarith only [mul_nonneg (by positivity : 0 ≤ x^4) (by positivity : 0 ≤ y^4)]

private theorem small_scalar_component_bounds (r x y : ℝ) (hr : 0 ≤ r) (hru : r ≤ 18/25)
    (hx : |x| ≤ 22) (hy : 32 ≤ |y|) (j : Fin 3) :
    |evenSymmetricOffScalar r j x y| ≤ ![(30:ℝ),2,1] j*y^2 := by
  have hxy : |x| ≤ (11/16)*|y| := by linarith only [hx,hy]
  have hy0 := abs_nonneg y
  have hyquad := mul_nonneg hy0 (sub_nonneg.mpr hy)
  have hs := symmetric_scalar_absolute_bounds r x y hr
  fin_cases j
  · change |evenSymmetricOffScalar r 0 x y| ≤ 30*y^2
    calc
      _ ≤ r*(45*|x| * |y|+(15/4)*(|x|+|y|)^2) := hs.1
      _ ≤ (18/25)*(45*((11/16)*|y|) * |y|+(15/4)*((11/16)*|y|+|y|)^2) := by gcongr
      _ ≤ _ := by nlinarith only [sq_abs y,sq_nonneg y]
  · change |evenSymmetricOffScalar r 1 x y| ≤ 2*y^2
    calc
      _ ≤ 45*r*(|x|+|y|) := hs.2.1
      _ ≤ 45*(18/25)*((11/16)*|y|+|y|) := by gcongr
      _ ≤ _ := by nlinarith only [sq_abs y,hyquad,hy0]
  · change |evenSymmetricOffScalar r 2 x y| ≤ 1*y^2
    simpa only [one_mul] using hs.2.2.trans (by nlinarith only [hru,sq_abs y,hyquad,hy] : 45*r ≤ y^2)

theorem even_symmetric_small_scalar_bound (r x y δ : ℝ) (hr : 0 ≤ r) (hru : r ≤ 18/25)
    (hx : |x| ≤ 22) (hy : 32 ≤ |y|) (hδ : 1/16 ≤ δ) :
    (∑ j : Fin 3, (evenSymmetricOffScalar r j x y)^2) ≤ 15000*δ*y^4 := by
  calc
    _ ≤ ∑ j : Fin 3, (![(30:ℝ),2,1] j*y^2)^2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := pow_le_pow_left₀ (abs_nonneg (evenSymmetricOffScalar r j x y))
        (small_scalar_component_bounds r x y hr hru hx hy j) 2
      simpa only [sq_abs] using h
    _ = 905*y^4 := by
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val,
        Matrix.head_cons,Matrix.tail_cons,Fin.sum_univ_zero,add_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hδ]) (by positivity : 0 ≤ y^4)

end Lemniscate
