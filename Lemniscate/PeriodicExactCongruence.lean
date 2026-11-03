import Lemniscate.PeriodicReducedCongruence
import Lemniscate.PeriodicCenteredStableForm
import Lemniscate.PeriodicExactFormComparison

/-! Identify the reduced form with the actual centered Bloch energy,
using exact kernel cancellation before making the finite approximation. -/
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
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
    (ψ : circleH4Domain T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T))
include he hqreal hpreal hs hc ho hr hd

theorem paper_exact_reduced_as_centered (α : ℝ) (f g : circleH4Domain T) :
    circleExactReducedBlochPairing T q p hq hp ψ α f g =
      circleReducedBlochForm T (fun j => circleDomainSymmetricPairing T
        (circleCenteredCoefficientLinear T q p hq hp (ψ:CircleL2 T) j)) α f g := by
  have horth (v : circleH4Domain T) : inner ℂ (circleHouseholderAnchor T)
      ((v-circleFixedProjectionH4 T v:circleH4Domain T):CircleL2 T) = 0 := by
    simp only [circleFixedProjectionH4,Submodule.coe_sub,Submodule.coe_smul_of_tower,
      circle_householder_anchor_h4_coe,inner_sub_right,inner_smul_right,
      circle_householder_anchor_unit,mul_one,sub_self]
  simp only [circleExactReducedBlochPairing,circleReducedBlochForm,circleExactSymmetricCoefficient,
    Fin.reduceEq,ite_true,ite_false]
  rw [← paper_centered_zero_stable_form T q p hq hp he hqreal hpreal hs hc ho hr (ψ:CircleL2 T) hd
    (f-circleFixedProjectionH4 T f) (g-circleFixedProjectionH4 T g) (horth f) (horth g)]
  rfl

set_option maxHeartbeats 1000000 in
theorem paper_exact_centered_energy_congruence
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hsector : InCircleEvenSineSector T (ψ:CircleL2 T))
    (α : ℝ) (f : circleH4Domain T) :
    (inner ℂ (f:CircleL2 T) (circleCenteredBlochOperator T q p hq hp (ψ:CircleL2 T) α f)).re =
    (circleExactReducedBlochPairing T q p hq hp ψ α (circleCenterDilation T α f) (circleCenterDilation T α f)).re := by
  let A := circleCenteredCoefficientLinear T q p hq hp (ψ:CircleL2 T)
  have h0c : A 0 (circleHouseholderAnchorH4 T) = 0 := by
    change circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) 0 _ = 0
    rw [circle_centered_bloch_zero]
    exact paper_centered_operator_zero_column T q p hq hp he hqreal hpreal hs hc ho hr _ hd
  have h0r (v : circleH4Domain T) : inner ℂ (circleHouseholderAnchor T) (A 0 v) = 0 := by
    change inner ℂ (circleHouseholderAnchor T) (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) 0 v) = 0
    rw [circle_centered_bloch_zero]
    exact paper_centered_operator_zero_row T q p hq hp he hqreal hpreal hs hc ho hr _ hd v
  have hodd (j : Fin 5) (hj : Odd (j:ℕ)) :
      inner ℂ (circleHouseholderAnchor T) (A j (circleHouseholderAnchorH4 T)) = 0 :=
    paper_centered_bloch_odd_anchor_zero T q p hq hp he hqreal hpreal hs hc ho hr _ hnorm hsector j hj
  have h4 (v : circleH4Domain T) : A 4 v = ((-4*(2*Real.pi/T)^4:ℝ):ℂ) • (v:CircleL2 T) := by
    change circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) 4 v = _
    have ht := paper_centered_bloch_top T q p hq hp he hqreal hpreal hs hc ho hr _ hd v
    have hpow : lemniscateFrequencySquared^2 = (2*Real.pi/T)^4 := by rw [← hr]; ring
    simpa only [hpow] using ht
  let P := A 0+(α:ℂ) • A 1+(α:ℂ)^2 • A 2+(α:ℂ)^3 • A 3+(α:ℂ)^4 • A 4
  have hop : P f = circleCenteredBlochOperator T q p hq hp (ψ:CircleL2 T) α f := by
    simp only [P,A,LinearMap.add_apply,LinearMap.smul_apply,circle_centered_coefficient_linear_apply]
    exact (circle_centered_bloch_polynomial T q p hq hp (ψ:CircleL2 T) α f).symm
  have hg := circle_reduced_center_congruence T A h0c h0r (hodd 1 (by decide)) (hodd 3 (by decide)) h4 α f
  have hsym := hg.trans (paper_exact_reduced_as_centered T q p hq hp he hqreal hpreal hs hc ho hr ψ hd
    α (circleCenterDilation T α f) (circleCenterDilation T α f)).symm
  have hr := congrArg Complex.re hsym
  rw [circle_domain_symmetric_energy] at hr
  rw [hop] at hr
  exact hr

end Profile
end Lemniscate
