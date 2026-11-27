import Migration.LowDefectInverseWeights
import Migration.LowDefectNormalCorrection

noncomputable section
open Set MeasureTheory Finset
namespace MigrationGeometry.Flow.LowDefect.Tangent

def farSize (G : ℝ→ℂ) (n : ℤ) : ℝ :=
  if n=0 ∨ n=1 ∨ n=2 then 0 else ‖coeff G n‖

/-- Absolute mass of all position harmonics except the constant,
first, and second. The coefficients belong to the actual position. -/
theorem far_position_bound {G T : ℝ→ℂ} {D : ℝ} (ct : Continuous T)
    (dg : ∀x,HasDerivAt G ((2*Real.pi:ℂ)*T x) x)
    (per : G 1=G 0) (hd : HasSum (fun n : ℤ => ((n:ℝ)-1)^2*energy T n) D) :
    Summable (farSize G) ∧ (∑'n,farSize G n)≤(575/1000)*Real.sqrt D := by
  let A := fun n : ℤ => ((n:ℝ)-1)^2*energy T n
  have pos (n) : 0≤A n := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have wp (n) : 0 ≤ inverseWeight n := by unfold inverseWeight;split_ifs <;> positivity
  have fp (n) : 0≤farSize G n := by unfold farSize; split_ifs <;> positivity
  have eq (n : ℤ) : farSize G n=Real.sqrt (A n)*Real.sqrt (inverseWeight n) := by
    by_cases ex : n=0 ∨ n=1 ∨ n=2
    · simp [farSize,inverseWeight,ex]
    have n0 : n≠0 := by omega
    have n1 : n≠1 := by omega
    have nz : (n:ℝ)≠0 := by exact_mod_cast n0
    have nz1 : (n:ℝ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast n1)
    apply (sq_eq_sq₀ (fp n) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt (pos n),Real.sq_sqrt (wp n)]
    simp only [farSize,inverseWeight,if_neg ex,A,energy,position_coefficient ct dg per n0,
      norm_mul,norm_div,norm_neg,Complex.norm_I,Complex.norm_intCast,mul_pow,div_pow,sq_abs]
    field_simp
  have bound (s : Finset ℤ) : (∑n ∈ s,farSize G n)≤(575/1000)*Real.sqrt D := by
    simp_rw [eq]
    have cum : (∑n ∈ s,A n)≤D := by
      rw [←hd.tsum_eq]
      exact hd.summable.sum_le_tsum _ (fun n _ => pos n)
    have w := (inverseWeight_sum.1.sum_le_tsum s (fun n _ => wp n)).trans inverseWeight_sum.2
    have v : Real.sqrt (∑n ∈ s,inverseWeight n) ≤ 575/1000 :=
      (Real.sqrt_le_sqrt w).trans_eq (Real.sqrt_sq (by norm_num))
    exact (Real.sum_sqrt_mul_sqrt_le s pos wp).trans (by
      rw [mul_comm (575/1000:ℝ)]
      exact mul_le_mul (Real.sqrt_le_sqrt cum) v (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  exact ⟨summable_of_sum_le fp bound,Real.tsum_le_of_sum_le fp bound⟩

end MigrationGeometry.Flow.LowDefect.Tangent
#print axioms MigrationGeometry.Flow.LowDefect.Tangent.far_position_bound
