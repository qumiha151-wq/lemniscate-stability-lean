import Lemniscate.PeriodicAngularH4Norm
import Lemniscate.NeutralHouseholder

/-! Error bounds for the actual Householder formula, in L2 and in the
angular H4 sum norm. Only the errors of its defining vectors enter. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_norm_le_angular_h4 (f : circleH4Domain T) :
    ‖f‖ ≤ circleAngularH4Norm T f := by
  have hT : 0 < T := Fact.out
  change ‖(f : CircleL2 T)‖ ≤ _
  unfold circleAngularH4Norm
  have h1 : 0 ≤ (2*Real.pi/T)⁻¹*‖(circleH4Jet T f).first‖ := by positivity
  have h2 : 0 ≤ ((2*Real.pi/T)⁻¹)^2*‖(circleH4Jet T f).second‖ := by positivity
  have h3 : 0 ≤ ((2*Real.pi/T)⁻¹)^3*‖(circleH4Jet T f).third‖ := by positivity
  have h4 : 0 ≤ ((2*Real.pi/T)⁻¹)^4*‖(circleH4Jet T f).fourth‖ := by positivity
  linarith only [h1,h2,h3,h4]

theorem circle_angular_h4_norm_neg (f : circleH4Domain T) :
    circleAngularH4Norm T (-f) = circleAngularH4Norm T f := by
  simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using
    circle_angular_h4_norm_smul T (-1) f

theorem circle_angular_h4_norm_sub_le (f g : circleH4Domain T) :
    circleAngularH4Norm T (f-g) ≤ circleAngularH4Norm T f+circleAngularH4Norm T g := by
  simpa only [sub_eq_add_neg,circle_angular_h4_norm_neg] using
    circle_angular_h4_norm_add_le T f (-g)

set_option maxHeartbeats 1000000 in
theorem circle_householder_difference_bounds (e eN a f : circleH4Domain T)
    (ε : ℝ) (hε : 0 ≤ ε) (he : ‖e‖ ≤ 1) (heN : ‖eN‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (huN : circleAngularH4Norm T (eN+a) ≤ 231)
    (herr : circleAngularH4Norm T (e-eN) ≤ ε)
    (hd : 1 ≤ ‖1+inner ℂ (e:CircleL2 T) (a:CircleL2 T)‖)
    (hdN : 1 ≤ ‖1+inner ℂ (eN:CircleL2 T) (a:CircleL2 T)‖) :
    circleAngularH4Norm T (neutralHouseholderDomain e a f-neutralHouseholderDomain eN a f)
      ≤ 695*ε*‖f‖ ∧
    ‖neutralHouseholderDomain e a f-neutralHouseholderDomain eN a f‖ ≤ 8*ε*‖f‖ := by
  let d := 1+inner ℂ (e:CircleL2 T) (a:CircleL2 T)
  let dN := 1+inner ℂ (eN:CircleL2 T) (a:CircleL2 T)
  let b := d⁻¹*inner ℂ ((e:CircleL2 T)+(a:CircleL2 T)) (f:CircleL2 T)
  let bN := dN⁻¹*inner ℂ ((eN:CircleL2 T)+(a:CircleL2 T)) (f:CircleL2 T)
  have hδ : ‖e-eN‖ ≤ ε := (circle_norm_le_angular_h4 T _).trans herr
  have hu : ‖e+a‖ ≤ 2 := by linarith only [norm_add_le e a,he,ha]
  have huN0 : ‖eN+a‖ ≤ 2 := by linarith only [norm_add_le eN a,heN,ha]
  have hdi : ‖d⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hd
  have hdNi : ‖dN⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hdN
  have hd0 : d ≠ 0 := by intro hz; change 1 ≤ ‖d‖ at hd; norm_num [hz] at hd
  have hdN0 : dN ≠ 0 := by intro hz; change 1 ≤ ‖dN‖ at hdN; norm_num [hz] at hdN
  have hdd : ‖d-dN‖ ≤ ε := by
    have hid : d-dN = inner ℂ ((e-eN:circleH4Domain T):CircleL2 T) (a:CircleL2 T) := by
      simp only [d,dN,Submodule.coe_sub,inner_sub_left]
      ring
    rw [hid]
    have hh := norm_inner_le_norm (𝕜 := ℂ) ((e-eN:circleH4Domain T):CircleL2 T) (a:CircleL2 T)
    change ‖inner ℂ ((e-eN:circleH4Domain T):CircleL2 T) (a:CircleL2 T)‖ ≤ ‖e-eN‖*‖a‖ at hh
    exact hh.trans ((mul_le_mul hδ ha (norm_nonneg _) hε).trans_eq (mul_one ε))
  have hdiδ : ‖d⁻¹-dN⁻¹‖ ≤ ε := by
    have hid : d⁻¹-dN⁻¹ = d⁻¹*(dN-d)*dN⁻¹ := by field_simp
    rw [hid,norm_mul,norm_mul,norm_sub_rev dN d]
    have hm := mul_le_mul hdi hdd (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simp only [one_mul] at hm
    have hm' := mul_le_mul hm hdNi (norm_nonneg _) hε
    simpa only [one_mul,mul_one] using hm'
  have hb : ‖b‖ ≤ 2*‖f‖ := by
    have hh := norm_inner_le_norm (𝕜 := ℂ) ((e:CircleL2 T)+(a:CircleL2 T)) (f:CircleL2 T)
    change ‖inner ℂ ((e:CircleL2 T)+(a:CircleL2 T)) (f:CircleL2 T)‖ ≤ ‖e+a‖*‖f‖ at hh
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hu (norm_nonneg f))
    have hm := mul_le_mul hdi hh' (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simpa only [b,norm_mul,one_mul] using hm
  have hbδ : ‖b-bN‖ ≤ 3*ε*‖f‖ := by
    have hid : b-bN = d⁻¹*inner ℂ ((e-eN:circleH4Domain T):CircleL2 T) (f:CircleL2 T)+
        (d⁻¹-dN⁻¹)*inner ℂ ((eN:CircleL2 T)+(a:CircleL2 T)) (f:CircleL2 T) := by
      simp only [b,bN,Submodule.coe_sub,inner_sub_left,inner_add_left]
      ring
    have hh := norm_inner_le_norm (𝕜 := ℂ) ((e-eN:circleH4Domain T):CircleL2 T) (f:CircleL2 T)
    change ‖inner ℂ ((e-eN:circleH4Domain T):CircleL2 T) (f:CircleL2 T)‖ ≤ ‖e-eN‖*‖f‖ at hh
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg f))
    have hk := norm_inner_le_norm (𝕜 := ℂ) ((eN:CircleL2 T)+(a:CircleL2 T)) (f:CircleL2 T)
    change ‖inner ℂ ((eN:CircleL2 T)+(a:CircleL2 T)) (f:CircleL2 T)‖ ≤ ‖eN+a‖*‖f‖ at hk
    have hk' := hk.trans (mul_le_mul_of_nonneg_right huN0 (norm_nonneg f))
    have h1 := mul_le_mul hdi hh' (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have h2 := mul_le_mul hdiδ hk' (norm_nonneg _) hε
    rw [hid]
    have ht := norm_add_le (d⁻¹*inner ℂ ((e-eN:circleH4Domain T):CircleL2 T) (f:CircleL2 T))
      ((d⁻¹-dN⁻¹)*inner ℂ ((eN:CircleL2 T)+(a:CircleL2 T)) (f:CircleL2 T))
    simp only [norm_mul,one_mul] at ht h1 h2
    nlinarith only [ht,h1,h2]
  have hid : neutralHouseholderDomain e a f-neutralHouseholderDomain eN a f =
      -(b • (e-eN))-(b-bN) • (eN+a) := by
    dsimp only [neutralHouseholderDomain,b,bN,d,dN]
    module
  rw [hid]
  constructor
  · have ht := circle_angular_h4_norm_sub_le T (-(b • (e-eN))) ((b-bN) • (eN+a))
    rw [circle_angular_h4_norm_neg,circle_angular_h4_norm_smul,circle_angular_h4_norm_smul] at ht
    have h1 := mul_le_mul hb herr (circle_angular_h4_norm_nonneg T _) (by positivity : 0 ≤ 2*‖f‖)
    have h2 := mul_le_mul hbδ huN (circle_angular_h4_norm_nonneg T _) (by positivity : 0 ≤ 3*ε*‖f‖)
    nlinarith only [ht,h1,h2]
  · have ht := norm_sub_le (-(b • (e-eN))) ((b-bN) • (eN+a))
    simp only [norm_neg,norm_smul] at ht
    have h1 := mul_le_mul hb hδ (norm_nonneg _) (by positivity : 0 ≤ 2*‖f‖)
    have h2 := mul_le_mul hbδ huN0 (norm_nonneg _) (by positivity : 0 ≤ 3*ε*‖f‖)
    nlinarith only [ht,h1,h2]

end Lemniscate
