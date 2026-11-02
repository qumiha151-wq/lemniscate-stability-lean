import Lemniscate.PeriodicProfileBlochSpectrum
import Lemniscate.PeriodicFrequencyProjection
import Lemniscate.PeriodicBlochReflection
import Lemniscate.PeriodicBlochEvenEigenvector

/-! The uniform Bloch spectral bound for the actual H4-domain operator.
Eigenvectors are split by Fourier parity; reflection handles negative
parameters. The spectral set retains its bounded-inverse definition. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

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

private theorem profile_positive_bloch_eigenvalue_bound
    (α : ℝ) (hα0 : 0 ≤ α) (hαhalf : α ≤ 1/2)
    (f : circleH4Domain T) (hfne : (f:CircleL2 T) ≠ 0) (w : ℂ)
    (hAf : circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f =
      w • (f:CircleL2 T)) : w.re ≤ -(1/2:ℝ)*α^2 := by
  have ho₀ (n : ℤ) (hn : Odd n) : fourierCoeff (q^2 : C(AddCircle T, ℂ)) n = 0 := by
    obtain ⟨k,hk⟩ := (odd_frequency_range n).mpr hn
    rw [← hk,ho]
  have hd₀ := circle_profile_square_deriv T q p hq
  have hd₁ := circle_profile_square_second T q p hq hp he
  have ho₁ (n : ℤ) (hn : Odd n) : fourierCoeff ((2:ℂ) • (q*p)) n = 0 := by
    rw [fourierCoeff_classical_deriv T _ _ hd₀,ho₀ n hn,mul_zero]
  have ho₂ (n : ℤ) (hn : Odd n) :
      fourierCoeff (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) n = 0 := by
    rw [fourierCoeff_classical_deriv T _ _ hd₁,ho₁ n hn,mul_zero]
  let g := circleEvenProjectionH4 T f
  have hgeig : circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α g =
      w • (g:CircleL2 T) := by
    rw [circle_even_projection_bloch T _ _ _ ho₀ ho₁ ho₂ α f,hAf,map_smul]
    rfl
  by_cases hgne : (g:CircleL2 T) = 0
  · have hproj : circleEvenProjection T (f:CircleL2 T) = 0 := hgne
    have hfodd := circle_odd_remainder_is_odd T (f:CircleL2 T)
    rw [hproj,sub_zero] at hfodd
    have hb := paper_odd_bloch_eigenvalue_bound T q p hq hp he hs hc hr α hα0 hαhalf
      f hfne hfodd w hAf
    nlinarith only [hb,hα0,hαhalf]
  · exact paper_even_bloch_eigenvalue_bound T q p hq hp he hqreal hpreal hs hc ho hr
      α hα0 hαhalf g hgne (circle_even_projection_is_even T (f:CircleL2 T)) w hgeig

theorem paper_uniform_bloch_spectral_bound
    (α : ℝ) (hα : |α| ≤ 1/2) (w : ℂ)
    (hw : w ∈ circleBlochSpectrum T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α) :
    w.re ≤ -(1/2:ℝ)*α^2 := by
  obtain ⟨f,hfne,hAf⟩ :=
    (paper_bloch_spectrum_iff_eigenvector T q p he hqreal hpreal hr α hα w).mp hw
  obtain ⟨hαlo,hαhi⟩ := abs_le.mp hα
  by_cases hα0 : 0 ≤ α
  · exact profile_positive_bloch_eigenvalue_bound T q p hq hp he hqreal hpreal hs hc ho hr
      α hα0 hαhi f hfne w hAf
  · obtain ⟨hrefne,hrefeig⟩ := circle_bloch_reflected_eigenvector T _ _ _
      (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
      hs α w f hfne hAf
    have hb := profile_positive_bloch_eigenvalue_bound T q p hq hp he hqreal hpreal hs hc ho hr
      (-α) (by linarith) (by linarith) (circleReflectH4 T f) hrefne w hrefeig
    simpa only [neg_sq] using hb

end Profile
end Lemniscate
