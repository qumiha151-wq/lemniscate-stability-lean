import Lemniscate.PeriodicH2Fourier

/-! Identify the weighted cosine coefficient domain with the periodic Sobolev
domain defined by two weak derivatives. This still does not identify the
coefficient quadratic form with the paper's geometric differential operator. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

theorem circle_cosine_weak_second_coefficients (v : CosineSequenceSpace) (g : CircleL2 T)
    (hfg : HasWeakCircleSecond T (circleEvenCosineSynthesis T v) g) (j : ℕ) :
    fourierCoeff g (2*(j:ℤ)) =
      (((2*Real.pi/T)^2:ℝ):ℂ)*evenCosineFactor*
        evenSecondCoefficients (fun k => v k) j := by
  by_cases hj : j = 0
  · subst j
    rw [fourier_of_weak_circle_second T _ g hfg]
    simp [evenSecondCoefficients]
  · rw [fourier_of_weak_circle_second T _ g hfg,
      circle_even_cosine_coeff_pos T v j (Nat.pos_of_ne_zero hj)]
    unfold evenSecondCoefficients
    push_cast
    ring

theorem circle_cosine_h2_coefficients_of_weak_second (v : CosineSequenceSpace)
    (g : CircleL2 T) (hfg : HasWeakCircleSecond T (circleEvenCosineSynthesis T v) g) :
    HasH2Coefficients (fun j => v j) := by
  apply (h2_coefficients_iff_second_l2 _).mpr
  refine ⟨lp.memℓp v, ?_⟩
  have hi : Function.Injective (fun j : ℕ => 2*(j:ℤ)) := by
    intro a b h
    change 2*(a:ℤ) = 2*(b:ℤ) at h
    omega
  have hs := (circle_fourier_square_summable T g).comp_injective hi
  have hm : Memℓp (fun j : ℕ => fourierCoeff g (2*(j:ℤ))) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Function.comp_def] using hs
  let d : ℂ := (((2*Real.pi/T)^2:ℝ):ℂ)*evenCosineFactor
  have hc : evenCosineFactor ≠ 0 := by
    intro h
    have hn := evenCosineFactor_normalization
    rw [h] at hn
    norm_num at hn
  have hd : d ≠ 0 := by
    apply mul_ne_zero _ hc
    have hT : T ≠ 0 := ne_of_gt (Fact.out : 0 < T)
    have hk : (2*Real.pi/T)^2 ≠ 0 :=
      pow_ne_zero 2 (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hT)
    exact_mod_cast hk
  have hm' := hm.const_mul d⁻¹
  have heq : (fun j : ℕ => d⁻¹*fourierCoeff g (2*(j:ℤ))) =
      evenSecondCoefficients (fun j => v j) := by
    funext j
    rw [circle_cosine_weak_second_coefficients T v g hfg]
    change d⁻¹*(d*evenSecondCoefficients (fun k => v k) j) = _
    rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  rw [heq] at hm'
  exact hm'

theorem circle_cosine_mem_h2_iff (v : CosineSequenceSpace) :
    InCircleH2 T (circleEvenCosineSynthesis T v) ↔ HasH2Coefficients (fun j => v j) := by
  constructor
  · intro h
    obtain ⟨g, hfg⟩ := (circle_h2_iff_weak_second T _).mp h
    exact circle_cosine_h2_coefficients_of_weak_second T v g hfg
  · intro hv
    have heq : h2Sequence (fun j => v j) hv = v := by
      ext j
      rfl
    simpa only [h2CircleFunction, heq] using h2_circle_function_mem_h2 T _ hv

theorem circle_cosine_sobolev_energy_bound (v : CosineSequenceSpace)
    (hv : InCircleH2 T (circleEvenCosineSynthesis T v)) :
    cosineH2Form (fun j => v j) ≤ -(21/4:ℝ)*‖circleEvenCosineSynthesis T v‖^2 :=
  circle_even_cosine_energy_bound T v ((circle_cosine_mem_h2_iff T v).mp hv)

end Lemniscate
