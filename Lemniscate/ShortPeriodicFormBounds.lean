import Lemniscate.ShortBlochFormBounds
import Lemniscate.ShortSobolevNorm

/-! The short form constants hold on the actual periodic function spaces.
All derivative bounds are derived from their Fourier norms. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem short_angular_frequency_bounds
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared) :
    shortAngularFrequency T ≤ 17/20 ∧ shortAngularFrequency T ^ 2 ≤ 359/500 := by
  have hp : 0 < 2*Real.pi/T := short_angular_frequency_pos T
  have hn : ‖circleFrequencyFactor T 1‖ = shortAngularFrequency T := by
    simp only [circleFrequencyFactor,shortAngularFrequency,Int.cast_one,mul_one,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,abs_of_pos hp]
  simpa only [hn] using short_circle_frequency_bounds T hr

theorem short_even_derivative_bounds
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
    (f : circleH4Domain T)
    (hf : ∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n = 0) :
    ‖(f:CircleL2 T)‖ ≤ shortVNorm T f ∧
      ‖(circleH4Jet T f).first‖ ≤ (17/40:ℝ)*shortVNorm T f ∧
      ‖(circleH4Jet T f).second‖ ≤ (359/500:ℝ)*shortVNorm T f := by
  have hk := short_angular_frequency_bounds T hr
  have hc := short_v_controls T f
  refine ⟨hc.1,?_,?_⟩
  · have hm := mul_le_mul_of_nonneg_right hk.1 (short_v_norm_nonneg T f)
    have hd := short_v_even_first_control T f hf
    nlinarith only [hm,hd]
  · exact hc.2.trans (mul_le_mul_of_nonneg_right hk.2 (short_v_norm_nonneg T f))

theorem short_periodic_positive_form_bounds
    (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
    (f g : circleH4Domain T)
    (hf : ∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n = 0) :
    ‖inner ℂ (g:CircleL2 T)
      (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) 1 f)‖ ≤
        70*shortVNorm T f*shortH1Norm T g ∧
    ‖inner ℂ (g:CircleL2 T)
      (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) 2 f)‖ ≤
        45*shortVNorm T f*shortH1Norm T g ∧
    ‖inner ℂ (g:CircleL2 T)
      (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) 3 f)‖ ≤
        5*shortVNorm T f*shortH1Norm T g := by
  have hc := short_profile_coefficient_bounds T q p he hqreal hpreal
  have hk := short_circle_frequency_bounds T hr
  have hka := short_angular_frequency_bounds T hr
  have hd := short_even_derivative_bounds T hr f hf
  have hg := short_h1_controls T g
  have hg₁ : ‖(circleH4Jet T g).first‖ ≤ (17/20:ℝ)*shortH1Norm T g :=
    hg.2.trans (mul_le_mul_of_nonneg_right hka.1 (short_h1_norm_nonneg T g))
  refine ⟨?_,?_,?_⟩
  · exact short_bloch_one_form_bound T _ _ _ hc.1 hc.2.1 hk.1 f g _ _
      hd.1 hd.2.1 hd.2.2 hg.1 hg₁
  · exact short_bloch_two_form_bound T _ _ _ hc.1 hk.2 f g _ _ hd.1 hd.2.2 hg.1
  · exact short_bloch_three_form_bound T _ _ _ hk.1 hk.2 f g _ _
      (short_v_norm_nonneg T f) hd.2.1 hg.1

theorem short_periodic_symmetric_form_bound
    (q p : C(AddCircle T, ℂ)) (hq : HasCircleDeriv T q p)
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
    (f g : circleH4Domain T)
    (hf : ∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n = 0)
    (hg : ∀ n : ℤ, Odd n → fourierCoeff (g:CircleL2 T) n = 0) :
    ‖inner ℂ (g:CircleL2 T)
      (circleH4SymmetricOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f)‖ ≤
        60*shortVNorm T f*shortVNorm T g := by
  have hc := short_profile_coefficient_bounds T q p he hqreal hpreal
  have hdf := short_even_derivative_bounds T hr f hf
  have hdg := short_even_derivative_bounds T hr g hg
  apply short_symmetric_form_bound T _ _ _ (circle_profile_square_deriv T q p hq)
    _ _ hc.1 hc.2.2 f g _ _ hdf.1 hdf.2.1 hdf.2.2 hdg.1 hdg.2.1 hdg.2.2
  · intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow,hqreal]
  · intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul,map_ofNat,hqreal,hpreal]

end Lemniscate
