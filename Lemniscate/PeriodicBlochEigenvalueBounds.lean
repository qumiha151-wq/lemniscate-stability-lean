import Lemniscate.PeriodicCenteredEvenEnergy
import Lemniscate.PeriodicBlochOddLimit

/-! Eigenvalue bounds obtained directly from the proved energy inequalities.
The even estimate uses only the forward dilation and the orthogonal norm
identity; no inverse dilation or division by the Bloch parameter is needed. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

private theorem eigenvalue_real_pairing (f : CircleL2 T) (w : ℂ) :
    (inner ℂ f (w • f)).re = w.re*‖f‖^2 := by
  have hself : inner ℂ f f = ((‖f‖^2:ℝ):ℂ) := by simp [inner_self_eq_norm_sq_to_K]
  rw [inner_smul_right,hself]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

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

include he hqreal hpreal hs hc ho hr in
theorem paper_centered_even_eigenvalue_bound (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T))
    (α : ℝ) (hα0 : 0 ≤ α) (hαhalf : α ≤ 1/2)
    (f : circleH4Domain T) (hfne : (f:CircleL2 T) ≠ 0)
    (hf : ∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n = 0)
    (w : ℂ) (hAf : circleCenteredBlochOperator T q p hq hp (ψ:CircleL2 T) α f =
      w • (f:CircleL2 T)) : w.re ≤ -(1/2:ℝ)*α^2 := by
  have h := paper_centered_even_energy T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hnorm hzero hd α hα0 hαhalf f hf
  rw [hAf,eigenvalue_real_pairing] at h
  have hsplit := circle_fixed_projection_l2_norm_split T f
  change ‖f-circleFixedProjectionH4 T f‖^2+‖circleFixedProjectionH4 T f‖^2 =
    ‖(f:CircleL2 T)‖^2 at hsplit
  have hscaled := congrArg (fun x : ℝ => α^2*x) hsplit
  have hrest : 0 ≤ (1-α^2)*‖f-circleFixedProjectionH4 T f‖^2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  have hnpos : 0 < ‖(f:CircleL2 T)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hfne)
  apply (mul_le_mul_iff_left₀ hnpos).mp
  change w.re*‖(f:CircleL2 T)‖^2 ≤ (-(1/2:ℝ)*α^2)*‖(f:CircleL2 T)‖^2
  nlinarith only [h,hscaled,hrest]

include hq hp he hs hc hr in
theorem paper_odd_bloch_eigenvalue_bound
    (α : ℝ) (hα0 : 0 ≤ α) (hαhalf : α ≤ 1/2)
    (f : circleH4Domain T) (hfne : (f:CircleL2 T) ≠ 0)
    (hf : InCircleOddSector T (f:CircleL2 T)) (w : ℂ)
    (hAf : circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f =
      w • (f:CircleL2 T)) : w.re ≤ -1 := by
  have h := paper_h4_bloch_odd_dissipative T q p hq hp he hs hc hr α hα0 hαhalf f hf
  rw [hAf,eigenvalue_real_pairing] at h
  have hnpos : 0 < ‖(f:CircleL2 T)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hfne)
  apply (mul_le_mul_iff_left₀ hnpos).mp
  linarith only [h]

end Profile
end Lemniscate
