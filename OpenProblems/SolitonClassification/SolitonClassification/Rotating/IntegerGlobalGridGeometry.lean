import SolitonClassification.Rotating.IntegerGlobalCrossingGeometry

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCrossings
open Set
noncomputable section

theorem unit_coordinate_motion {b L : ℝ} (I : WindingOneImmersion b L) (s t : ℝ) :
    |I.x t-I.x s|≤|t-s| ∧ |I.y t-I.y s|≤|t-s| := by
  have lip (f g : ℝ→ℝ) (df : ∀w,HasDerivAt f (g w) w) (unit : ∀w,|g w|≤1) :
      |f t-f s|≤|t-s| := by
    have r := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun w _ => (df w).differentiableAt)
      (fun w _ => by rw [(df w).deriv,Real.norm_eq_abs];exact unit w) (mem_univ s) (mem_univ t)
    simpa only [Real.norm_eq_abs,one_mul] using r
  exact ⟨lip I.x _ I.tangentX (fun _=>Real.abs_cos_le_one _),lip I.y _ I.tangentY (fun _=>Real.abs_sin_le_one _)⟩

/-- Near rectangles of the signed 8,000-step covering contain only diagonal
or seam repetitions. The nominal number of steps can differ from the true
period in grid coordinates by one thousandth. -/
theorem short_grid_aliases {b L : ℝ} (I : WindingOneImmersion b L) (cap : ∀w,|I.k w|≤10)
    {h H u v : ℝ} (hp : 0<h) (step : h≤1/125) (period : L=H*h)
    (err : |H-8000|≤1/1000) (hu : -4001≤u) (hv : v≤4001) (ord : u≤v)
    (near : v-u≤32 ∨ 7970≤v-u) (same : (I.x (u*h),I.y (u*h))=(I.x (v*h),I.y (v*h))) :
    u=v ∨ (v-u)*h=L := by
  rcases eq_or_lt_of_le ord with eq | lt
  · exact Or.inl eq
  right
  rcases near with close | wrap
  · exfalso
    apply short_arc_ne I (mul_lt_mul_of_pos_right lt hp) _ (fun w _=>cap w) same
    rw [←sub_mul]
    exact (mul_le_mul close step hp.le (by norm_num : (0:ℝ)≤32)).trans (by norm_num)
  by_contra ne
  have expr : v*h+(-1:ℤ)•L-u*h=(v-u-H)*h := by
    rw [period];simp only [neg_smul,one_smul];ring
  have nz : v*h+(-1:ℤ)•L-u*h≠0 := by
    intro zero
    apply ne
    simp only [neg_smul,one_smul] at zero
    linarith only [zero]
  have count : |v-u-H|≤31 := by
    obtain ⟨lo,hi⟩ := abs_le.mp err
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have bd : |v*h+(-1:ℤ)•L-u*h|≤3/10 := by
    rw [expr,abs_mul,abs_of_pos hp]
    exact (mul_le_mul count step hp.le (by norm_num : (0:ℝ)≤31)).trans (by norm_num)
  exact (short_modulo_period_ne I cap (-1) (abs_pos.mpr nz) bd) same

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCrossings
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCrossings.short_grid_aliases
