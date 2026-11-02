import Lemniscate.ActualEvenHeadEnergy
import Lemniscate.PeriodicAnalyticCoupling
import Lemniscate.PeriodicHighFourthLower
import Lemniscate.PeriodicProfileCoefficientBounds

/-! Full even-frequency coercivity of the finite neutral approximation,
combining the actual head, the complete high tail, and analytic coupling.
Concrete identification of the profile Fourier series remains explicit. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
set_option maxHeartbeats 1000000
variable (T : ℝ) [Fact (0 < T)]

theorem paper_finite_even_coercivity (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter)
    (α : ℝ) (hα0 : 0 ≤ α) (hαhalf : α ≤ 1/2)
    (f : circleH4Domain T)
    (hf : ∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n = 0) :
    (circleFiniteBlochPairing T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f f).re ≤
      -‖(f:CircleL2 T)‖^2 := by
  let h := q^2
  let h₁ := (2:ℂ) • (q*p)
  let h₂ := 1-(3:ℂ) • (q^4)
  let v (i : Fin 31) := fourierCoeff (f:CircleL2 T) (evenHeadFrequency i)
  let u := circleEvenHeadProjection T f
  let y := f-u
  let D : ℝ := ∑ i : Fin 31, (evenFactorPenalty i:ℝ)*‖v i‖^2
  let W : ℝ := ∑' n : ℤ, (n:ℝ)^4*‖fourierCoeff (y:CircleL2 T) n‖^2
  have hh : HasCircleDeriv T h h₁ := circle_profile_square_deriv T q p hq
  have hh₁ : HasCircleDeriv T h₁ h₂ := circle_profile_square_second T q p hq hp he
  have hreal : ∀ x, conj (h x) = h x := by
    intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow,hqreal]
  have h₁real : ∀ x, conj (h₁ x) = h₁ x := by
    intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul,map_ofNat,hqreal,hpreal]
  have h₂real : ∀ x, conj (h₂ x) = h₂ x := by
    intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub,map_mul,map_one,map_ofNat,map_pow,hqreal]
  have hnorm : ‖h‖ ≤ 1 ∧ ‖h₁‖ ≤ 2 ∧ ‖h₂‖ ≤ 4 :=
    circle_profile_coefficient_norm_bounds T q p he hqreal hpreal
  have hparam : (7/10:ℝ) ≤ (2*Real.pi/T)^2 ∧ (2*Real.pi/T)^2 ≤ 18/25 := by
    rw [hr]
    have hb : Contains ⟨thetaRLower,thetaRUpper⟩ thetaParameter := actual_nome_theta_r_bounds
    refine ⟨?_,?_⟩
    · exact (by norm_num [thetaRLower] : (7/10:ℝ) ≤ (thetaRLower:ℝ)).trans hb.1
    · exact hb.2.trans (by norm_num [thetaRUpper])
  have hα : |α| ≤ 1/2 := abs_le.mpr ⟨by linarith only [hα0],hαhalf⟩
  have hyhigh : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (y:CircleL2 T) n = 0 :=
    circle_even_head_remainder_high T f hf
  have hyeven (n : ℤ) (hn : ¬Even n) : fourierCoeff (y:CircleL2 T) n = 0 := by
    have hodd := Int.not_even_iff_odd.mp hn
    change fourierCoeff ((f:CircleL2 T)-(u:CircleL2 T)) n = 0
    rw [circle_fourierCoeff_sub,hf n hodd]
    have hz : fourierCoeff (u:CircleL2 T) n = 0 := by
      apply circle_even_head_fourier_outside T v n
      intro i hi
      exact hn ((even_head_frequency_range n).mp ⟨i,hi.symm⟩).1
    rw [hz,sub_self]
  have hD : 0 ≤ D := by
    apply Finset.sum_nonneg
    intro i _
    have hd : (0:ℚ) ≤ evenFactorPenalty i := by
      rw [even_factor_penalty_values i]
      exact (by norm_num : (0:ℚ) ≤ 1/16).trans (even_mode_penalty_lower _)
    exact mul_nonneg (Rat.cast_nonneg.mpr hd) (sq_nonneg _)
  have hW : 0 ≤ W := tsum_nonneg (fun n => mul_nonneg (by positivity) (sq_nonneg _))
  have hhead := actual_finite_even_head_energy T h h₁ h₂ hh hh₁ hs hc hr α hα0 hαhalf v
  have hnormu : ‖(u:CircleL2 T)‖^2 = ∑ i : Fin 31, ‖v i‖^2 := circle_even_head_norm_sq T v
  have hlow : (circleFiniteBlochPairing T h h₁ h₂ α u u).re ≤ -‖(u:CircleL2 T)‖^2-D := by
    calc
      _ ≤ ∑ i : Fin 31, (-1-(evenFactorPenalty i:ℝ))*‖v i‖^2 := hhead
      _ = -(∑ i : Fin 31, ‖v i‖^2)-D := by
        simp only [D,sub_mul,neg_mul,one_mul,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
      _ = _ := by rw [hnormu]
  have hhigh := paper_finite_bloch_high_energy T q p hq hp he hqreal hpreal hparam.1 α hα y hyhigh
  have hcross := circle_finite_analytic_coupling T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hparam.2
    hnorm.1 hnorm.2.1 hnorm.2.2 α hα v y hyeven hyhigh
  change (circleFiniteBlochPairing T h h₁ h₂ α y y).re ≤ -(1/2:ℝ)*W at hhigh
  change ‖circleFiniteBlochPairing T h h₁ h₂ α u y‖^2 ≤ (D/4)*W at hcross
  have hre : (circleFiniteBlochPairing T h h₁ h₂ α u y).re^2 ≤
      ‖circleFiniteBlochPairing T h h₁ h₂ α u y‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith only [sq_nonneg (circleFiniteBlochPairing T h h₁ h₂ α u y).im]
  have hb : (circleFiniteBlochPairing T h h₁ h₂ α u y).re^2 ≤ D*(W/2)/2 := by
    nlinarith only [hre,hcross]
  have hfourth := circle_high_fourth_weight_lower T y hyhigh
  change 4*‖(y:CircleL2 T)‖^2 ≤ W at hfourth
  have hbound := finite_tail_energy_bound
    (circleFiniteBlochPairing T h h₁ h₂ α u u).re
    (circleFiniteBlochPairing T h h₁ h₂ α u y).re
    (circleFiniteBlochPairing T h h₁ h₂ α y y).re
    (‖(u:CircleL2 T)‖^2) (‖(y:CircleL2 T)‖^2) D (W/2)
    hD (by positivity) (by linarith only [hfourth]) hlow (by linarith only [hhigh]) hb
  have hsplit := circle_finite_bloch_head_remainder_energy T h h₁ h₂ α f
  have hnormsplit := circle_even_head_norm_decomposition T f
  change (circleFiniteBlochPairing T h h₁ h₂ α f f).re =
    (circleFiniteBlochPairing T h h₁ h₂ α u u).re+2*(circleFiniteBlochPairing T h h₁ h₂ α u y).re+
      (circleFiniteBlochPairing T h h₁ h₂ α y y).re at hsplit
  change ‖(f:CircleL2 T)‖^2 = ‖(u:CircleL2 T)‖^2+‖(y:CircleL2 T)‖^2 at hnormsplit
  change (circleFiniteBlochPairing T h h₁ h₂ α f f).re ≤ _
  nlinarith only [hbound,hsplit,hnormsplit]

end Lemniscate
