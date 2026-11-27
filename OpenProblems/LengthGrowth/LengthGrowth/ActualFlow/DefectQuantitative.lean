import LengthGrowth.ActualFlow.DefectExplicitLength

noncomputable section
namespace LengthGrowth.BendingSublevel

/-- Sharp GN bounds the whole optimized expression without taking a square
root of the derivative moment. Valid even when Q or V vanishes. -/
theorem optimized_fourth {I V Q : ℝ} (v0 : 0≤V) (q0 : 0≤Q)
    (gn : 3*I^2≤V^3*Q) : I/2-Q≤V^3/48 := by
  suffices h : I≤2*Q+V^3/24 by linarith
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith only [gn,sq_nonneg (2*Q-V^3/24)]

/-- Physical moment estimates on the slice of length 2π imply a quadratic
lower bound for the normalized dissipative rate. -/
theorem quadratic_rate {P B σ V I₃ I₄ Q e : ℝ}
    (e0 : 0≤e) (q0 : 0≤Q) (v0 : 0≤V) (hs : 1≤σ)
    (mass : B=P+V) (variance : V=P*(σ^2-1))
    (bc : 2≤B) (vc : V≤900/157) (coef : 69/100≤5/2-σ-1/(σ+1))
    (cub : 2*(P+3*V+I₃)≤B*(1+σ)+4*Real.sqrt e)
    (vir : B-4*e/B ≤ -2*Q+P+6*V+4*I₃+I₄)
    (gn : 3*I₄^2≤V^3*Q) : V^2/1000000≤e := by
  have nz : σ+1≠0 := by linarith
  have id : B*(1+σ)-2*P-6*V=V*(σ+1/(σ+1)-5) := by
    rw [mass,variance]; field_simp [nz]; ring
  have j : 2*I₃≤V*(σ+1/(σ+1)-5)+4*Real.sqrt e := by linarith only [id,cub]
  have low : (69/100)*V ≤ I₄/2-Q+4*Real.sqrt e+2*e/B := by
    have hcoef := mul_le_mul_of_nonneg_right coef v0
    simp only [div_eq_mul_inv] at hcoef vir j ⊢
    linarith only [hcoef,vir,mass,j]
  have vmax := pow_le_pow_left₀ v0 vc 2
  have margin : V^2/48≤69/100-1/200 := by linarith only [vmax]
  have sharp := optimized_fourth v0 q0 gn
  have small : V/200≤4*Real.sqrt e+2*e/B := by
    linarith only [low,sharp,mul_le_mul_of_nonneg_right margin v0]
  have vs : V/1000≤Real.sqrt e := by
    by_contra! bad
    have rt := Real.sqrt_nonneg e
    have pow := Real.sq_sqrt e0
    have cap : Real.sqrt e≤1 := by linarith only [vc,bad]
    have er : e≤Real.sqrt e := by nlinarith only [pow,mul_nonneg rt (sub_nonneg.mpr cap)]
    have quot : 2*e/B≤e := (div_le_iff₀ (by linarith : 0<B)).mpr (by
      linarith only [mul_le_mul_of_nonneg_right bc e0])
    linarith only [bad,small,quot,er]
  have square := pow_le_pow_left₀ (show 0≤V/1000 by positivity) vs 2
  rw [Real.sq_sqrt e0] at square
  linarith only [square]

end LengthGrowth.BendingSublevel
#print axioms LengthGrowth.BendingSublevel.quadratic_rate
