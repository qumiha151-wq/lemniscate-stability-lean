import Lemniscate.PeriodicCoverComponents
import Lemniscate.PeriodicCoverOperator
import Lemniscate.PeriodicBlochSpectrumBound

/-! The lower spectral gap on every finite cover. Periodic extension is
specified by the Fourier coefficients of the original coefficient; neither
a spectral decomposition nor a spectral bound on the cover is assumed. -/
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
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)
include hq hp he hqreal hpreal hs hc ho hr

theorem paper_cover_nonzero_spectral_bound (M : ℕ) (hM : 2 ≤ M) (hS : S = (M:ℝ)*T)
    (H H₁ H₂ : C(AddCircle S, ℂ))
    (hD : HasCircleDeriv S H H₁) (hD₁ : HasCircleDeriv S H₁ H₂)
    (hmulti : ∀ n : ℤ, fourierCoeff H ((M:ℤ)*n) = fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hvanish : ∀ n : ℤ, ¬(M:ℤ) ∣ n → fourierCoeff H n = 0)
    (w : ℂ) (hwne : w ≠ 0) (hw : w ∈ circleSpectrum S H H₁ H₂) :
    w.re ≤ -(1/(2*(M:ℝ)^2)) := by
  have hMpos : 0 < M := by omega
  obtain ⟨f,hf,hAf⟩ := (circle_spectrum_iff_eigenvector S H H₁ H₂ w).mp hw
  obtain ⟨j,hj,hC⟩ := circle_cover_nonzero_component T S M hMpos (f:CircleL2 S) hf
  let g := circleCoverComponentH4 T S M hMpos hS j f
  have hgne : (g:CircleL2 T) ≠ 0 := hC
  have hgeig : circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      ((j:ℝ)/(M:ℝ)) g = w • (g:CircleL2 T) := by
    have h := congrArg (circleCoverComponent T S M hMpos j) hAf
    rw [circle_cover_operator_intertwine T S M hMpos hS _ _ _ H H₁ H₂
      (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
      hD hD₁ hmulti hvanish] at h
    simpa only [g,map_smul,circle_cover_component_h4_coe] using h
  have hα := circle_cover_parameter_bound M hMpos j hj
  have hspec := (paper_bloch_spectrum_iff_eigenvector T q p he hqreal hpreal hr
    ((j:ℝ)/(M:ℝ)) hα w).mpr ⟨g,hgne,hgeig⟩
  have hMr : (0:ℝ) < M := by exact_mod_cast hMpos
  by_cases hj0 : j = 0
  · have hspec₀ : w ∈ circleSpectrum T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) := by
      simpa only [hj0,Int.cast_zero,zero_div,circle_bloch_spectrum_at_zero] using hspec
    have hb := paper_single_period_nonzero_spectral_bound T q p hq hp he hqreal hpreal hs hc ho hr w hwne hspec₀
    have hMge : (2:ℝ) ≤ M := by exact_mod_cast hM
    have hgap : 1/(2*(M:ℝ)^2) ≤ (21/4:ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 2*(M:ℝ)^2)).mpr
      nlinarith only [hMge,sq_nonneg ((M:ℝ)-1)]
    linarith only [hb,hgap]
  · have hjabs : (1:ℤ) ≤ |j| := by
      have hpj := abs_pos.mpr hj0
      omega
    have hdist : 1/(M:ℝ) ≤ |(j:ℝ)/(M:ℝ)| := by
      rw [abs_div,abs_of_pos hMr]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hjabs) hMr.le
    have hgap := multiple_cover_gap (M:ℝ) ((j:ℝ)/(M:ℝ)) hMr hdist
    have hb := paper_uniform_bloch_spectral_bound T q p hq hp he hqreal hpreal hs hc ho hr
      ((j:ℝ)/(M:ℝ)) hα w hspec
    linarith only [hb,hgap]

end Profile
end Lemniscate
