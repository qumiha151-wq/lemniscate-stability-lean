import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

noncomputable section
namespace ClosedSimilarity.RamifiedBounded

def diskConstant (a b:ℂ) := Real.sqrt (2592+2*‖a‖+8*‖b‖)

theorem diskConstant_one (a b:ℂ) : 1≤diskConstant a b := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  linarith only [norm_nonneg a,norm_nonneg b]

theorem scaled_disk_bound {a b u v w j l:ℂ} {d:ℝ} (dp:0<d) (d1:d≤1)
    (vB:‖v‖≤4*‖u‖/d) (wB:‖w‖≤16*‖u‖/d^2) (jB:‖j‖≤96*‖u‖/d^3)
    (lB:‖l‖≤768*‖u‖/d^4)
    (eq:2*(u*l-v*j)+(3*(u^2*v^2)+5*(u^3*w))+u^6-2*a*u^2-2*b*v=0) :
    d*‖u‖≤diskConstant a b := by
  let A:=d*‖u‖
  change A≤_
  by_cases small : A≤1
  · exact small.trans (diskConstant_one a b)
  have ha : 1≤A := le_of_not_ge small
  have a0 : 0≤A := zero_le_one.trans ha
  have relation : u^6= -(2*u*l)+(2*v*j)+(-(3*u^2*v^2))+(-(5*u^3*w))+(2*a*u^2)+(2*b*v) := by
    linear_combination eq
  have tri : ‖u‖^6≤2*‖u‖*‖l‖+2*‖v‖*‖j‖+3*‖u‖^2*‖v‖^2+5*‖u‖^3*‖w‖+2*‖a‖*‖u‖^2+2*‖b‖*‖v‖ := by
    rw [←norm_pow,relation]
    calc _ ≤ ‖-(2*u*l)‖+‖2*v*j‖+‖-(3*u^2*v^2)‖+‖-(5*u^3*w)‖+‖2*a*u^2‖+‖2*b*v‖ := by
                grw [norm_add_le,norm_add_le,norm_add_le,norm_add_le,norm_add_le]
         _ = _ := by simp [norm_pow]
  have weighted : A^6≤2304*A^2+128*A^4+2*‖a‖*A^2*d^4+8*‖b‖*A*d^4 := by
    calc A^6 = d^6*‖u‖^6 := mul_pow _ _ _
         _ ≤ d^6*(2*‖u‖*(768*‖u‖/d^4)+2*(4*‖u‖/d)*(96*‖u‖/d^3)+
             3*‖u‖^2*(4*‖u‖/d)^2+5*‖u‖^3*(16*‖u‖/d^2)+2*‖a‖*‖u‖^2+2*‖b‖*(4*‖u‖/d)) := by
               apply mul_le_mul_of_nonneg_left _ (by positivity)
               apply tri.trans
               gcongr
         _ = _ := by dsimp [A];field_simp;ring
  have h2 : A^2≤A^4 := pow_le_pow_right₀ ha (by decide)
  have h1 : A≤A^4 := by simpa using (pow_le_pow_right₀ ha (show 1≤4 by decide))
  have d4 : d^4≤1 := pow_le_one₀ dp.le d1
  have e1 : 2*‖a‖*A^2*d^4≤2*‖a‖*A^4*1 := by gcongr
  have e2 : 8*‖b‖*A*d^4≤8*‖b‖*A^4*1 := by gcongr
  have hsq : A^2≤2592+2*‖a‖+8*‖b‖ := by
    apply le_of_mul_le_mul_right (a:=A^4) _ (pow_pos (lt_of_lt_of_le zero_lt_one ha) _)
    calc A^2*A^4 = A^6 := by ring
         _ ≤ _ := weighted
         _ ≤ (2592+2*‖a‖+8*‖b‖)*A^4 := by nlinarith only [h2,e1,e2,pow_nonneg a0 4]
  exact (Real.le_sqrt a0 (by positivity)).mpr hsq

#print axioms scaled_disk_bound
end ClosedSimilarity.RamifiedBounded
