import Migration.LowDefectMaterialCorrection

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.LowDefect

/-- Centroid flux in fractional arclength. The quadratic inequality keeps
the sharp sum of the two L² bounds, including the case D=0. -/
theorem flux_norm_sq {K : ℝ→ℝ} {G Z : ℝ→ℂ} (ck : Continuous K)
    (cg : Continuous G) (cz : Continuous Z) {M D : ℝ} (mp : 0≤M)
    (bound : ∀x∈Icc (0:ℝ) 1, ‖G x‖≤M)
    (kv : (∫x in (0:ℝ)..1,K x^2)=D)
    (zv : (∫x in (0:ℝ)..1,‖Z x‖^2)≤(75/100)^2*D) :
    (∫x in (0:ℝ)..1,‖K x • G x+Z x‖^2) ≤ (M+75/100)^2*D := by
  let f := fun x => ‖K x • G x+Z x‖^2
  let g := fun x => (M+75/100)*(M*K x^2+(4/3)*‖Z x‖^2)
  have cf : Continuous f := (((ck.smul cg).add cz).norm.pow 2)
  have cm : Continuous g := continuous_const.mul ((continuous_const.mul (ck.pow 2)).add (continuous_const.mul (cz.norm.pow 2)))
  have le (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : f x≤g x := by
    have a := norm_add_le (K x • G x) (Z x)
    rw [norm_smul,Real.norm_eq_abs] at a
    have b := mul_le_mul_of_nonneg_left (bound x hx) (abs_nonneg (K x))
    have q := pow_le_pow_left₀ (norm_nonneg _) (a.trans (add_le_add b le_rfl)) 2
    change ‖K x • G x+Z x‖^2 ≤ (M+75/100)*(M*K x^2+(4/3)*‖Z x‖^2)
    have eq : K x^2=|K x|^2 := (sq_abs _).symm
    rw [eq]
    nlinarith only [q,mul_nonneg mp (sq_nonneg ((75/100)*|K x|-‖Z x‖))]
  have scalar := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ)≤1)
    (cf.intervalIntegrable ..) (cm.intervalIntegrable ..) le
  change (∫x in (0:ℝ)..1,f x) ≤ _
  apply scalar.trans
  dsimp only [g]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (f:=fun x=>M*K x^2) (g:=fun x=>(4/3)*‖Z x‖^2)
      ((continuous_const.mul (ck.pow 2)).intervalIntegrable ..)
      ((continuous_const.mul (cz.norm.pow 2)).intervalIntegrable ..),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,kv]
  have bz := mul_le_mul_of_nonneg_left zv (by linarith : 0≤(M+75/100)*(4/3))
  linarith

end MigrationGeometry.Flow.LowDefect
#print axioms MigrationGeometry.Flow.LowDefect.flux_norm_sq
