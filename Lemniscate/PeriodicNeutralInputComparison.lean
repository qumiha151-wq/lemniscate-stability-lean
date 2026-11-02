import Lemniscate.PeriodicHouseholderComparison
import Lemniscate.NeutralTransformAdjoints

/-! Compare the two domain inputs in the transformed bilinear form.
No derivative of the arbitrary argument is used in the error bound. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

private theorem pairing_sub_bound (u v uN vN : circleH4Domain T)
    (δ R S : ℝ) (hδ : 0 ≤ δ) (hS : 0 ≤ S)
    (hu : ‖u-uN‖ ≤ δ) (hv : ‖v‖ ≤ R) (huN : ‖uN‖ ≤ S)
    (hvδ : ‖v-vN‖ ≤ 8*δ*R) :
    ‖inner ℂ (u:CircleL2 T) (v:CircleL2 T)-inner ℂ (uN:CircleL2 T) (vN:CircleL2 T)‖
      ≤ δ*R+S*(8*δ*R) := by
  have hid : inner ℂ (u:CircleL2 T) (v:CircleL2 T)-inner ℂ (uN:CircleL2 T) (vN:CircleL2 T) =
      inner ℂ ((u-uN:circleH4Domain T):CircleL2 T) (v:CircleL2 T)+
        inner ℂ (uN:CircleL2 T) ((v-vN:circleH4Domain T):CircleL2 T) := by
    simp only [Submodule.coe_sub,inner_sub_left,inner_sub_right]
    ring
  rw [hid]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul hu hv (norm_nonneg _) hδ)
  · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul huN hvδ (norm_nonneg _) hS)

set_option maxHeartbeats 1000000 in
theorem circle_neutral_input_difference_bounds (e ψ eN ψN a f : circleH4Domain T)
    (ε : ℝ) (hε : 0 ≤ ε) (he : ‖e‖ ≤ 1) (heN : ‖eN‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (heNH4 : circleAngularH4Norm T eN ≤ 200)
    (hψNH4 : circleAngularH4Norm T ψN ≤ 200)
    (huNH4 : circleAngularH4Norm T (eN+a) ≤ 231)
    (heδ : circleAngularH4Norm T (e-eN) ≤ ε)
    (hψδ : circleAngularH4Norm T (ψ-ψN) ≤ ε)
    (hz : ‖ψ-e‖ ≤ 1) (hzN : ‖ψN-eN‖ ≤ 1)
    (hd : 1 ≤ ‖1+inner ℂ (e:CircleL2 T) (a:CircleL2 T)‖)
    (hdN : 1 ≤ ‖1+inner ℂ (eN:CircleL2 T) (a:CircleL2 T)‖)
    (hU : ‖neutralHouseholderDomain e a f‖ ≤ ‖f‖)
    (hUN : ‖neutralHouseholderDomain eN a f‖ ≤ ‖f‖) :
    let U := neutralHouseholderDomain e a f
    let UN := neutralHouseholderDomain eN a f
    let L := neutralTransformAdjointDomain e ψ U
    let LN := neutralTransformAdjointDomain eN ψN UN
    let R := neutralTransformInvDomain e (ψ:CircleL2 T) U
    let RN := neutralTransformInvDomain eN (ψN:CircleL2 T) UN
    circleAngularH4Norm T (L-LN) ≤ 5000*ε*‖f‖ ∧
    circleAngularH4Norm T (R-RN) ≤ 5000*ε*‖f‖ ∧
    ‖L‖ ≤ 2*‖f‖ ∧ ‖LN‖ ≤ 2*‖f‖ ∧ ‖R‖ ≤ 2*‖f‖ ∧ ‖RN‖ ≤ 2*‖f‖ := by
  let U := neutralHouseholderDomain e a f
  let UN := neutralHouseholderDomain eN a f
  let z := ψ-e
  let zN := ψN-eN
  let s := inner ℂ (e:CircleL2 T) (U:CircleL2 T)
  let sN := inner ℂ (eN:CircleL2 T) (UN:CircleL2 T)
  let c := inner ℂ (z:CircleL2 T) (U:CircleL2 T)
  let cN := inner ℂ (zN:CircleL2 T) (UN:CircleL2 T)
  rcases circle_householder_difference_bounds T e eN a f ε hε he heN ha huNH4 heδ hd hdN with ⟨hUH4,hUδ⟩
  change circleAngularH4Norm T (U-UN) ≤ 695*ε*‖f‖ at hUH4
  change ‖U-UN‖ ≤ 8*ε*‖f‖ at hUδ
  have heδ0 := (circle_norm_le_angular_h4 T (e-eN)).trans heδ
  have hzNH4 : circleAngularH4Norm T zN ≤ 400 := by
    have h := circle_angular_h4_norm_sub_le T ψN eN
    linarith only [h,heNH4,hψNH4]
  have hzδ : circleAngularH4Norm T (z-zN) ≤ 2*ε := by
    have hid : z-zN = (ψ-ψN)-(e-eN) := by dsimp only [z,zN]; abel
    rw [hid]
    have h := circle_angular_h4_norm_sub_le T (ψ-ψN) (e-eN)
    linarith only [h,heδ,hψδ]
  have hzδ0 := (circle_norm_le_angular_h4 T (z-zN)).trans hzδ
  have hcoef (u v : circleH4Domain T) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ ‖f‖) :
      ‖inner ℂ (u:CircleL2 T) (v:CircleL2 T)‖ ≤ ‖f‖ := by
    have h := (norm_inner_le_norm (𝕜 := ℂ) (u:CircleL2 T) (v:CircleL2 T)).trans
      (mul_le_mul hu hv (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
    simpa only [one_mul] using h
  have hs : ‖s‖ ≤ ‖f‖ := hcoef e U he hU
  have hsN : ‖sN‖ ≤ ‖f‖ := hcoef eN UN heN hUN
  have hc : ‖c‖ ≤ ‖f‖ := hcoef z U hz hU
  have hcN : ‖cN‖ ≤ ‖f‖ := hcoef zN UN hzN hUN
  have hsδ : ‖s-sN‖ ≤ 9*ε*‖f‖ := by
    have h := pairing_sub_bound T e U eN UN ε ‖f‖ 1 hε (by norm_num)
      heδ0 hU heN hUδ
    change ‖s-sN‖ ≤ ε*‖f‖+1*(8*ε*‖f‖) at h
    nlinarith only [h]
  have hcδ : ‖c-cN‖ ≤ 10*ε*‖f‖ := by
    have hid : c-cN = inner ℂ ((z-zN:circleH4Domain T):CircleL2 T) (U:CircleL2 T)+
        inner ℂ (zN:CircleL2 T) ((U-UN:circleH4Domain T):CircleL2 T) := by
      dsimp only [c,cN]
      simp only [Submodule.coe_sub,inner_sub_left,inner_sub_right]
      ring
    rw [hid]
    have h1 := (norm_inner_le_norm (𝕜 := ℂ) ((z-zN:circleH4Domain T):CircleL2 T) (U:CircleL2 T)).trans
      (mul_le_mul hzδ0 hU (norm_nonneg _) (by positivity : 0 ≤ 2*ε))
    have h2 := (norm_inner_le_norm (𝕜 := ℂ) (zN:CircleL2 T) ((U-UN:circleH4Domain T):CircleL2 T)).trans
      (mul_le_mul hzN hUδ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
    have ht := norm_add_le (inner ℂ ((z-zN:circleH4Domain T):CircleL2 T) (U:CircleL2 T))
      (inner ℂ (zN:CircleL2 T) ((U-UN:circleH4Domain T):CircleL2 T))
    nlinarith only [h1,h2,ht]
  have hLid : neutralTransformAdjointDomain e ψ U-neutralTransformAdjointDomain eN ψN UN =
      (U-UN)+(s • (z-zN)+(s-sN) • zN) := by
    dsimp only [neutralTransformAdjointDomain,LinearMap.coe_mk,AddHom.coe_mk,s,sN,z,zN]
    module
  have hRid : neutralTransformInvDomain e (ψ:CircleL2 T) U-
      neutralTransformInvDomain eN (ψN:CircleL2 T) UN =
        (U-UN)-(c • (e-eN)+(c-cN) • eN) := by
    dsimp only [neutralTransformInvDomain,c,cN,z,zN]
    simp only [Submodule.coe_sub]
    module
  have hLerr : circleAngularH4Norm T
      (neutralTransformAdjointDomain e ψ U-neutralTransformAdjointDomain eN ψN UN) ≤ 5000*ε*‖f‖ := by
    rw [hLid]
    have h1 := circle_angular_h4_norm_add_le T (U-UN) (s • (z-zN)+(s-sN) • zN)
    have h2 := circle_angular_h4_norm_add_le T (s • (z-zN)) ((s-sN) • zN)
    simp only [circle_angular_h4_norm_smul] at h2
    have h3 := mul_le_mul hs hzδ (circle_angular_h4_norm_nonneg T _) (norm_nonneg f)
    have h4 := mul_le_mul hsδ hzNH4 (circle_angular_h4_norm_nonneg T _) (by positivity : 0 ≤ 9*ε*‖f‖)
    nlinarith only [h1,h2,h3,h4,hUH4,mul_nonneg hε (norm_nonneg f)]
  have hRerr : circleAngularH4Norm T
      (neutralTransformInvDomain e (ψ:CircleL2 T) U-neutralTransformInvDomain eN (ψN:CircleL2 T) UN)
        ≤ 5000*ε*‖f‖ := by
    rw [hRid]
    have h1 := circle_angular_h4_norm_sub_le T (U-UN) (c • (e-eN)+(c-cN) • eN)
    have h2 := circle_angular_h4_norm_add_le T (c • (e-eN)) ((c-cN) • eN)
    simp only [circle_angular_h4_norm_smul] at h2
    have h3 := mul_le_mul hc heδ (circle_angular_h4_norm_nonneg T _) (norm_nonneg f)
    have h4 := mul_le_mul hcδ heNH4 (circle_angular_h4_norm_nonneg T _) (by positivity : 0 ≤ 10*ε*‖f‖)
    nlinarith only [h1,h2,h3,h4,hUH4,mul_nonneg hε (norm_nonneg f)]
  refine ⟨hLerr,hRerr,?_,?_,?_,?_⟩
  · change ‖U+s • z‖ ≤ _
    have h := norm_add_le U (s • z)
    rw [norm_smul] at h
    have hm := mul_le_mul hs hz (norm_nonneg _) (norm_nonneg f)
    nlinarith only [h,hm,hU]
  · change ‖UN+sN • zN‖ ≤ _
    have h := norm_add_le UN (sN • zN)
    rw [norm_smul] at h
    have hm := mul_le_mul hsN hzN (norm_nonneg _) (norm_nonneg f)
    nlinarith only [h,hm,hUN]
  · change ‖U-c • e‖ ≤ _
    have h := norm_sub_le U (c • e)
    rw [norm_smul] at h
    have hm := mul_le_mul hc he (norm_nonneg _) (norm_nonneg f)
    nlinarith only [h,hm,hU]
  · change ‖UN-cN • eN‖ ≤ _
    have h := norm_sub_le UN (cN • eN)
    rw [norm_smul] at h
    have hm := mul_le_mul hcN heN (norm_nonneg _) (norm_nonneg f)
    nlinarith only [h,hm,hUN]

end Lemniscate
