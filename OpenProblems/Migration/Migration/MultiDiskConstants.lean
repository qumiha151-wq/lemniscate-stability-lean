import Migration.LowDefectPhysicalDisk

namespace MigrationGeometry.MultiDisk
theorem drift_constant {x v : ℝ} (hx : 0≤x) (X : x≤1/4) (hv : 0≤v) (V : v≤1/2) :
    (1+x^2*v^2)*(1+x)*(x*(1+(1+91/50*x)*v)) ≤ (54/100)*(1+v^2/16) := by
  have xx := pow_le_pow_left₀ hx X 2
  have first : 1+x^2*v^2≤1+v^2/16 := by nlinarith [mul_le_mul_of_nonneg_right xx (sq_nonneg v)]
  have b : (1+91/50*x)*v≤(1+91/50*(1/4:ℝ))*(1/2) :=
    mul_le_mul (by linarith) V hv (by norm_num)
  have plus : 1+(1+91/50*x)*v≤1+(1+91/50*(1/4:ℝ))*(1/2) := by linarith only [b]
  have c := mul_le_mul X plus (by positivity : 0≤1+(1+91/50*x)*v) (by norm_num : (0:ℝ)≤1/4)
  have d := mul_le_mul (by linarith : 1+x≤5/4) c (by positivity) (by norm_num : (0:ℝ)≤5/4)
  rw [mul_assoc (1+x^2*v^2)]
  apply (mul_le_mul first (d.trans (by norm_num : (5/4:ℝ)*(1/4*(1+(1+91/50*(1/4))*(1/2)))≤54/100)) (by positivity) (by positivity)).trans_eq
  ring

theorem support_constant {x v : ℝ} (hx : 0≤x) (X : x≤1/4) (hv : 0≤v) (V : v≤1/2) :
    (109/200)*(1+v^2/16) ≤ (1+x^2*v^2)*(1-91/50*x) := by
  have vv := pow_le_pow_left₀ hv V 2
  have uv := mul_le_mul (show x+1/4≤1/2 by linarith) vv (sq_nonneg _) (by norm_num : (0:ℝ)≤1/2)
  have pos : 0≤91/50-(x+1/4)*v^2+91/50*v^2*(x^2+x/4+1/16) := by
    have : 0≤91/50*v^2*(x^2+x/4+1/16) := by positivity
    linarith
  have := mul_nonneg (sub_nonneg.mpr X) pos
  linarith only [this]

end MigrationGeometry.MultiDisk
#print axioms MigrationGeometry.MultiDisk.support_constant

