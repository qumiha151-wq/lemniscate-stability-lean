import Lemniscate.ShortHeadReducedIdentification
import Lemniscate.ShortOutsideReduced
import Lemniscate.ShortOutsideRawIdentification
import Lemniscate.ShortCircleHermitian

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0<T)]

section Coefficients
variable (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x,conj (h x)=h x) (h₁real : ∀ x,conj (h₁ x)=h₁ x)
    (h₂real : ∀ x,conj (h₂ x)=h₂ x)
    (hs : ∀ n : ℤ,fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ,fourierCoeff h (2*(j:ℤ))=(shortActualCoefficient j:ℂ))
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)

include hh hh₁ hreal h₁real h₂real hs hc hr in
theorem circle_short_bernstein_head_entry (j : Fin 5) (i k : Fin 15) :
    circleShortBernsteinPairing T h h₁ h₂ j
      (circleFourierH4 T (shortHeadFrequency i)) (circleFourierH4 T (shortHeadFrequency k))=
      (shortBernsteinHead lemniscateFrequencySquared shortActualCoefficient j i k:ℂ) := by
  rw [← circle_short_head_single T i,← circle_short_head_single T k,
    circle_short_bernstein_head_pairing T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr]
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,shortHeadPair,Pi.single_apply]
  simp [shortComplexMatrix]

include hh hh₁ hreal h₁real h₂real hs hc hr in
theorem circle_short_bernstein_kernel (j : Fin 5) (n m : ℤ) :
    circleShortBernsteinPairing T h h₁ h₂ j
      (circleFourierH4 T (2*n)) (circleFourierH4 T (2*m))=
      (shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j n m:ℂ) := by
  cases hn : shortHeadIndex n with
  | none =>
    cases hm : shortHeadIndex m with
    | none =>
      simp only [shortBernsteinKernel,hn,hm]
      exact circle_short_bernstein_outside_pairing T h h₁ h₂ hh hh₁ hreal h₁real h₂real
        hs hc hr j n m hn hm
    | some i =>
      simp only [shortBernsteinKernel,hn,hm]
      rw [← circle_short_bernstein_conj T h h₁ h₂ hh hh₁ hreal h₁real h₂real,
        ← short_head_index_frequency m i hm,
        circle_short_bernstein_outside_column T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr _ _ n hn,
        Complex.conj_ofReal]
  | some i =>
    cases hm : shortHeadIndex m with
    | none =>
      simp only [shortBernsteinKernel,hn,hm]
      rw [← short_head_index_frequency n i hn]
      exact circle_short_bernstein_outside_column T h h₁ h₂ hh hh₁ hreal h₁real h₂real
        hs hc hr j i m hm
    | some k =>
      simp only [shortBernsteinKernel,hn,hm]
      rw [← short_head_index_frequency n i hn,← short_head_index_frequency m k hm]
      exact circle_short_bernstein_head_entry T h h₁ h₂ hh hh₁ hreal h₁real h₂real
        hs hc hr j i k

end Coefficients
end Lemniscate
