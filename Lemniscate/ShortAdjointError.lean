import Lemniscate.ShortAdjointEstimate
import Lemniscate.ShortAdjointPairing
import Lemniscate.ShortAdjointSineDuality

/-! Low-order errors of the actual normalized eight-mode trial. The residue
bound and the profile energy estimates are theorems, not numerical inputs. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def shortAdjointEnergyNorm (f : circleH4Domain T) : ℝ :=
  Real.sqrt ((13/100:ℝ)*(shortAngularFrequency T)⁻¹^4*
    ‖(circleH4Jet T f).second‖^2+(75/2:ℝ)*‖(f:CircleL2 T)‖^2)

theorem short_circle_trial_sector :
    InCircleEvenSineSector T (circleShortAdjointTrial T:CircleL2 T) := by
  have hc (n : ℤ) : fourierCoeff (circleShortAdjointTrial T:CircleL2 T) n =
      ∑ i : Fin 8, (shortAdjointTrialCoeff i:ℂ)*
        fourierCoeff (circleEvenSineMode T i.val) n := by
    rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
    change inner ℂ (fourierBasis (T := T) n)
      (∑ i : Fin 8, (shortAdjointTrialCoeff i:ℂ) • circleEvenSineMode T i.val) = _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right,← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  constructor
  · intro n
    rw [hc,hc]
    simp only [circle_even_sine_mode_coeff_neg,mul_neg,Finset.sum_neg_distrib]
  · intro n
    rw [hc]
    simp only [circle_even_sine_mode_coeff_odd,mul_zero,Finset.sum_const_zero]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

theorem short_circle_weighted_coercivity (f : circleH4Domain T)
    (hf : InCircleEvenSineSector T (f:CircleL2 T))
    (horth : inner ℂ (circleContinuousL2 T (q*p)) (f:CircleL2 T) = 0) :
    shortAdjointEnergyNorm T f ^ 2 ≤
      -(inner ℂ (f:CircleL2 T) (circleH4Operator T (q^2) ((2:ℂ) • (q*p))
        (1-(3:ℂ) • (q^4)) f)).re := by
  let κ := shortAngularFrequency T
  let E := -(inner ℂ (f:CircleL2 T) (circleH4Operator T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) f)).re
  have hκ : κ ≠ 0 := (short_angular_frequency_pos T).ne'
  have hκr : κ^2 = lemniscateFrequencySquared := hr
  have hd := paper_h4_operator_even_sine_sector_dissipative T q p hq hp he
    hqreal hpreal hs hc ho hr f hf horth
  have hg := paper_h4_operator_garding T q p hq hp he hqreal hpreal f
  have hgap : 75*‖(f:CircleL2 T)‖^2 ≤ E := by dsimp only [E]; linarith
  have hcancel : lemniscateFrequencySquared^2 *
      (‖(circleH4Jet T f).second‖/κ^2)^2 = ‖(circleH4Jet T f).second‖^2 := by
    rw [← hκr]
    field_simp
  have hgard : 2*lemniscateFrequencySquared^2*(‖(circleH4Jet T f).second‖/κ^2)^2-
      (1719/8:ℝ)*‖(f:CircleL2 T)‖^2 ≤ E := by
    dsimp only [E]
    nlinarith [hcancel]
  have hrlo : (7177/10000:ℝ) ≤ lemniscateFrequencySquared := by
    have h := short_frequency_enclosure.1
    norm_num [shortFrequencyInterval] at h
    linarith
  have h := short_adjoint_weighted_coercivity lemniscateFrequencySquared
    ‖(f:CircleL2 T)‖ (‖(circleH4Jet T f).second‖/κ^2) E hrlo hgap hgard
  have harg : 0 ≤ (13/100:ℝ)*(shortAngularFrequency T)⁻¹^4*
      ‖(circleH4Jet T f).second‖^2+(75/2:ℝ)*‖(f:CircleL2 T)‖^2 := by positivity
  rw [shortAdjointEnergyNorm,Real.sq_sqrt harg]
  have heq : (13/100:ℝ)*(shortAngularFrequency T)⁻¹^4*
      ‖(circleH4Jet T f).second‖^2+(75/2:ℝ)*‖(f:CircleL2 T)‖^2 =
      (13/100:ℝ)*(‖(circleH4Jet T f).second‖/κ^2)^2+(75/2:ℝ)*‖(f:CircleL2 T)‖^2 := by
    change (13/100:ℝ)*κ⁻¹^4*_+_ = _
    field_simp
  rw [heq]
  exact h

/-- The actual normalized short trial has the low-order error bounds used
in the new rank-one comparison, with any common unit rotation phase. -/
theorem short_circle_adjoint_eight_mode_error
    (σ : ℂ) (hσ : ‖σ‖ = 1) (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ:CircleL2 T) (σ • circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hψsector : InCircleEvenSineSector T (ψ:CircleL2 T)) :
    let t := circleNormalizedTrial T (σ • circleUnitRotation T q p) (circleShortAdjointTrial T)
    let w := ψ-t
    ‖(w:CircleL2 T)‖ < (1/1200000:ℝ) ∧
      shortH1Norm T w < (1/300000:ℝ) ∧
      ‖(w:CircleL2 T)‖+(shortAngularFrequency T)⁻¹*‖(circleH4Jet T w).first‖+
        (shortAngularFrequency T)⁻¹^2*‖(circleH4Jet T w).second‖ < (31/1800000:ℝ) := by
  let t := circleNormalizedTrial T (σ • circleUnitRotation T q p) (circleShortAdjointTrial T)
  let w := ψ-t
  let R := circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) t
  let W := shortAdjointEnergyNorm T w
  have hκ : 0 < shortAngularFrequency T := short_angular_frequency_pos T
  have hpair := circle_short_trial_phase_pairing T q p hq hp he hqreal hpreal hs hc hr σ hσ
  have hpairne : inner ℂ (circleShortAdjointTrial T:CircleL2 T)
      (σ • circleUnitRotation T q p) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt (lt_trans (by norm_num : (0:ℝ) < 1) hpair)
  have htnorm := circle_normalized_trial_pairing T _ (circleShortAdjointTrial T) hpairne
  have htsector : InCircleEvenSineSector T (t:CircleL2 T) :=
    circle_even_sine_sector_smul T _ _ (short_circle_trial_sector T)
  have hwsector := circle_even_sine_sector_sub T _ _ hψsector htsector
  have hvnorm : inner ℂ (w:CircleL2 T) (σ • circleUnitRotation T q p) = 0 := by
    change inner ℂ ((ψ:CircleL2 T)-(t:CircleL2 T)) _ = 0
    rw [inner_sub_left,hψnorm,htnorm,sub_self]
  have hσne : σ ≠ 0 := norm_ne_zero_iff.mp (by rw [hσ]; norm_num)
  have hunitpair : inner ℂ (w:CircleL2 T) (circleUnitRotation T q p) = 0 := by
    rw [inner_smul_right] at hvnorm
    exact (mul_eq_zero.mp hvnorm).resolve_left hσne
  have horth : inner ℂ (circleContinuousL2 T (q*p)) (w:CircleL2 T) = 0 := by
    have hv : inner ℂ (circleUnitRotation T q p) (w:CircleL2 T) = 0 := by
      rw [← inner_conj_symm,hunitpair,map_zero]
    have hn : (‖circleContinuousL2 T (q*p)‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (circle_profile_rotation_ne_zero T q p hq hs hc ho))
    simp only [circleUnitRotation,inner_smul_left,map_inv₀,Complex.conj_ofReal] at hv
    exact (mul_eq_zero.mp hv).resolve_left (inv_ne_zero hn)
  have h0real : ∀ x, conj ((q^2 : C(AddCircle T,ℂ)) x) = (q^2 : C(AddCircle T,ℂ)) x := by
    intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow,hqreal]
  have h1real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
    intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul,map_ofNat,hqreal,hpreal]
  have h2real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T,ℂ)) x) =
      (1-(3:ℂ) • (q^4) : C(AddCircle T,ℂ)) x := by
    intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub,map_one,map_mul,map_ofNat,map_pow,hqreal]
  have hRsector : InCircleEvenSineSector T R := by
    dsimp only [R,t,circleNormalizedTrial]
    rw [map_smul]
    apply circle_even_sine_sector_smul
    exact circle_adjoint_sine_trial_sector T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
      (circle_profile_square_second T q p hq hp he) h0real h1real h2real hs ho 8 _
  have henergy := short_circle_weighted_coercivity T q p hq hp he hqreal hpreal
    hs hc ho hr w hwsector horth
  have hgreen := circle_adjoint_residual_energy T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
    (circle_profile_square_second T q p hq hp he) h0real h1real h2real ψ t hψzero
  have hdual := short_circle_weighted_adjoint_duality T w R hwsector hRsector
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hres0 : 0 ≤ circleShortResidualSquare T R := by
    unfold circleShortResidualSquare
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg (fun j => div_nonneg (sq_nonneg _) (short_residual_weight_pos _).le)
  have hres := circle_short_normalized_adjoint_residual_square T q p hq hp he hqreal
    hpreal hs hc hr σ hσ
  have hroot : Real.sqrt (circleShortResidualSquare T R) < (1/200000:ℝ) := by
    have hsq := Real.sq_sqrt hres0
    have hn := Real.sqrt_nonneg (circleShortResidualSquare T R)
    change circleShortResidualSquare T R < (1/200000:ℝ)^2 at hres
    nlinarith
  have hW : W ≤ Real.sqrt (circleShortResidualSquare T R) := by
    have hab := le_abs_self (inner ℂ (w:CircleL2 T) R).re
    change W^2 ≤ _ at henergy
    change |(inner ℂ (w:CircleL2 T) R).re| ≤ W*Real.sqrt _ at hdual
    change (inner ℂ (w:CircleL2 T) (circleH4Operator T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) w)).re = -(inner ℂ (w:CircleL2 T) R).re at hgreen
    by_cases hz : W = 0
    · rw [hz]
      exact Real.sqrt_nonneg _
    · have hpW : 0 < W := lt_of_le_of_ne hW0 (Ne.symm hz)
      nlinarith
  have hWlt : W < (1/200000:ℝ) := hW.trans_lt hroot
  let a := ‖(w:CircleL2 T)‖
  let b := (shortAngularFrequency T)⁻¹*‖(circleH4Jet T w).first‖
  let c := (shortAngularFrequency T)⁻¹^2*‖(circleH4Jet T w).second‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have harg : 0 ≤ (13/100:ℝ)*(shortAngularFrequency T)⁻¹^4*
      ‖(circleH4Jet T w).second‖^2+(75/2:ℝ)*‖(w:CircleL2 T)‖^2 := by positivity
  have hweighted : (13/100:ℝ)*c^2+(75/2:ℝ)*a^2 ≤ W^2 := by
    dsimp only [W,shortAdjointEnergyNorm]
    rw [Real.sq_sqrt harg]
    dsimp only [a,c]
    nlinarith
  have hweak : b^2 ≤ a*c := by
    have h := mul_le_mul_of_nonneg_left
      (circle_weak_derivative_norm_sq_product T _ _ _
        (circleH4Jet T w).hfirst (circleH4Jet T w).hsecond)
      (sq_nonneg (shortAngularFrequency T)⁻¹)
    dsimp only [a,b,c]
    nlinarith only [h]
  have hbounds := short_adjoint_sobolev_bounds a b c W W ha hb hc0 hW0 le_rfl hweighted hweak
  have hH1 : shortH1Norm T w ≤ a+b := by
    have hn := short_h1_norm_nonneg T w
    have hs : shortH1Norm T w^2 = a^2+b^2 := by
      dsimp only [a,b]
      rw [short_h1_norm_sq]
      ring
    nlinarith [mul_nonneg ha hb]
  change a < _ ∧ shortH1Norm T w < _ ∧ a+b+c < _
  exact ⟨by linarith [hbounds.1],by linarith [hbounds.2.2.2.1],
    by linarith [hbounds.2.2.2.2]⟩

end Profile
end Lemniscate
