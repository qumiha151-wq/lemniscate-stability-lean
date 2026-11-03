import Lemniscate.EvenMatrixIdentification
import Lemniscate.EvenFactorBound
import Lemniscate.FiniteBernsteinEnergy

/-! The certified finite even-sector energy estimate, with the actual
coefficient matrices rather than an interval-containment hypothesis. -/
namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

theorem actual_even_bernstein_energy (k : Fin 5) (v : Fin 31 → ℂ) :
    (headPair v (realHeadMatrixCast (realFiniteBlochBernstein lemniscateFrequencySquared nome k) *ᵥ v)).re ≤
      ∑ i, (-1-(evenFactorPenalty i:ℝ))*‖v i‖^2 := by
  have h := even_factor_certified_energy k _
    (real_finite_bloch_bernstein_symm lemniscateFrequencySquared nome k)
    (actual_even_bernstein_interval k) v
  have heq : headPair v
      (realHeadMatrixCast (realFiniteBlochBernstein lemniscateFrequencySquared nome k) *ᵥ v) =
      ∑ i, ∑ j, conj (v i)*(realFiniteBlochBernstein lemniscateFrequencySquared nome k i j:ℂ)*v j := by
    simp only [headPair, mulVec, dotProduct, real_head_matrix_cast_apply, Finset.mul_sum, mul_assoc]
  rw [heq]
  exact h

variable (T : ℝ) [Fact (0 < T)]
variable (h h₁ h₂ : C(AddCircle T, ℂ))
variable (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
variable (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
variable (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
  (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
variable (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hh hh₁ hs hc hr

theorem actual_finite_even_head_energy (α : ℝ) (ha : 0 ≤ α) (ha' : α ≤ 1/2)
    (v : Fin 31 → ℂ) :
    (circleFiniteBlochPairing T h h₁ h₂ α (circleEvenHeadH4 T v) (circleEvenHeadH4 T v)).re ≤
      ∑ i, (-1-(evenFactorPenalty i:ℝ))*‖v i‖^2 := by
  rw [circle_finite_bloch_head_pairing, finite_bloch_head_bernstein]
  apply head_pair_bernstein_upper_bound _ v α _ ha ha'
  intro k
  rw [← real_finite_bloch_bernstein_cast T h h₁ h₂ lemniscateFrequencySquared nome hh hh₁ hs hc hr]
  exact actual_even_bernstein_energy k v

end Lemniscate
