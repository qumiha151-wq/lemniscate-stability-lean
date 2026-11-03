import Lemniscate.PeriodicCoverSpectralBound

/-! Zero Bloch components determine the kernel on a cover. The single-period
absence of generalized rotational eigenvectors then transfers directly, with
no inverse Fourier decomposition or additional adjoint construction. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

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
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (H H₁ H₂ : C(AddCircle S, ℂ))
    (hD : HasCircleDeriv S H H₁) (hD₁ : HasCircleDeriv S H₁ H₂)
    (hmulti : ∀ n : ℤ, fourierCoeff H ((M:ℤ)*n) = fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hvanish : ∀ n : ℤ, ¬(M:ℤ) ∣ n → fourierCoeff H n = 0)
include hq hp he hqreal hpreal hs hc ho hr hM hS hD hD₁ hmulti hvanish

private theorem kernel_component_vanish (f : circleH4Domain S)
    (hf : circleH4Operator S H H₁ H₂ f = 0) (j : ℤ) (hj : 2*|j| ≤ (M:ℤ)) (hj0 : j ≠ 0) :
    circleCoverComponent T S M hM j (f:CircleL2 S) = 0 := by
  by_contra hC
  let g := circleCoverComponentH4 T S M hM hS j f
  have hgeig : circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      ((j:ℝ)/(M:ℝ)) g = 0 := by
    have h := congrArg (circleCoverComponent T S M hM j) hf
    rw [circle_cover_operator_intertwine T S M hM hS _ _ _ H H₁ H₂
      (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
      hD hD₁ hmulti hvanish] at h
    simpa only [g,map_zero] using h
  have hα := circle_cover_parameter_bound M hM j hj
  have hspec := (paper_bloch_spectrum_iff_eigenvector T q p he hqreal hpreal hr
    ((j:ℝ)/(M:ℝ)) hα 0).mpr ⟨g,hC,by simpa only [zero_smul] using hgeig⟩
  have hb := paper_uniform_bloch_spectral_bound T q p hq hp he hqreal hpreal hs hc ho hr
    ((j:ℝ)/(M:ℝ)) hα 0 hspec
  have hMr : (M:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hαne : (j:ℝ)/(M:ℝ) ≠ 0 := div_ne_zero (by exact_mod_cast hj0) hMr
  have hsq := sq_pos_of_ne_zero hαne
  norm_num only [Complex.zero_re] at hb
  nlinarith only [hb,hsq]

theorem paper_cover_kernel_zero_of_zero_component (f : circleH4Domain S)
    (hf : circleH4Operator S H H₁ H₂ f = 0)
    (hC : circleCoverComponent T S M hM 0 (f:CircleL2 S) = 0) : (f:CircleL2 S) = 0 := by
  by_contra hfne
  obtain ⟨j,hj,hjC⟩ := circle_cover_nonzero_component T S M hM (f:CircleL2 S) hfne
  by_cases hj0 : j = 0
  · subst j
    exact hjC hC
  · exact hjC (kernel_component_vanish T S q p hq hp he hqreal hpreal hs hc ho hr
      M hM hS H H₁ H₂ hD hD₁ hmulti hvanish f hf j hj hj0)

theorem paper_cover_no_generalized_kernel (f g : circleH4Domain S)
    (hfg : circleH4Operator S H H₁ H₂ f = (g:CircleL2 S))
    (hg : circleH4Operator S H H₁ H₂ g = 0) : circleH4Operator S H H₁ H₂ f = 0 := by
  have hinter (u : circleH4Domain S) :
      circleCoverComponent T S M hM 0 (circleH4Operator S H H₁ H₂ u) =
        circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
          (circleCoverComponentH4 T S M hM hS 0 u) := by
    simpa only [Int.cast_zero,zero_div,circle_bloch_at_zero] using
      circle_cover_operator_intertwine T S M hM hS _ _ _ H H₁ H₂
        (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
        hD hD₁ hmulti hvanish 0 u
  have hfg₀ := congrArg (circleCoverComponent T S M hM 0) hfg
  rw [hinter] at hfg₀
  have hg₀ := congrArg (circleCoverComponent T S M hM 0) hg
  rw [hinter,map_zero] at hg₀
  have hzero := paper_single_period_no_generalized_kernel T q p hq hp he hqreal hpreal hs hc ho hr
    (circleCoverComponentH4 T S M hM hS 0 f) (circleCoverComponentH4 T S M hM hS 0 g) hfg₀ hg₀
  have hCg : circleCoverComponent T S M hM 0 (g:CircleL2 S) = 0 := by
    rw [← hfg₀,hzero]
  have hgz := paper_cover_kernel_zero_of_zero_component T S q p hq hp he hqreal hpreal hs hc ho hr
    M hM hS H H₁ H₂ hD hD₁ hmulti hvanish g hg hCg
  rw [hfg,hgz]

end Profile
end Lemniscate
