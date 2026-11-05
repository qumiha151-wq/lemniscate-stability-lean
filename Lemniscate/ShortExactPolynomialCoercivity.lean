import Lemniscate.ShortSchurFourierCoercivity
import Lemniscate.ShortPolynomialNorm
import Lemniscate.ShortActualBernsteinComparison

/-! The actual exact Bernstein forms are nonpositive on every finite even
Fourier polynomial. Both the full Fourier kernel and the vector errors are
proved for the same seven-mode approximation. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0<T)]

theorem short_exact_polynomial_bernstein_nonpositive
    (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x,2*(p x)^2+(q x)^4=1)
    (hqreal : ∀ x,conj (q x)=q x) (hpreal : ∀ x,conj (p x)=p x)
    (hs : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (-n)=fourierCoeff (q^2:C(AddCircle T,ℂ)) n)
    (hc : ∀ j : ℕ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (2*(j:ℤ))=
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (2*n+1)=0)
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)
    (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p)=1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ=0)
    (j : Fin 5) (I : Finset ℤ) (a : ℤ → ℂ) :
    (circleShiftedBernsteinPairing T (circleExactSymmetricCoefficient T q p hq hp ψ) j
      (∑ n∈I,a n • circleFourierH4 T (2*n))
      (∑ n∈I,a n • circleFourierH4 T (2*n))).re≤0 := by
  let f : circleH4Domain T := ∑ n∈I,a n • circleFourierH4 T (2*n)
  have hf : f ∈ shortEvenDomain T := circle_short_polynomial_even T I a
  have h0real : ∀ x,conj ((q^2:C(AddCircle T,ℂ)) x)=(q^2:C(AddCircle T,ℂ)) x := by
    intro x
    change conj ((q x)^2)=(q x)^2
    simp only [map_pow,hqreal]
  have h1real : ∀ x,conj (((2:ℂ) • (q*p)) x)=((2:ℂ) • (q*p)) x := by
    intro x
    change conj (2*(q x*p x))=2*(q x*p x)
    simp only [map_mul,map_ofNat,hqreal,hpreal]
  have h2real : ∀ x,conj ((1-(3:ℂ) • (q^4):C(AddCircle T,ℂ)) x)=
      (1-(3:ℂ) • (q^4):C(AddCircle T,ℂ)) x := by
    intro x
    change conj (1-3*(q x)^4)=1-3*(q x)^4
    simp only [map_sub,map_mul,map_one,map_ofNat,map_pow,hqreal]
  have hkernel := circle_short_bernstein_polynomial T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
    (circle_profile_square_second T q p hq hp he) h0real h1real h2real hs hc hr j I I a a
  have hfinite := short_kernel_polynomial_coercivity j I a
  rw [← hkernel,← circle_short_polynomial_v_norm T I a] at hfinite
  have herror := short_actual_bernstein_form_error T q p hq hp he hqreal hpreal
    hs hc ho hr ψ hψnorm hψzero j f hf
  have hre := Complex.re_le_norm
    (circleShiftedBernsteinPairing T (circleExactSymmetricCoefficient T q p hq hp ψ) j f f-
      circleShortBernsteinPairing T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j f f)
  change (circleShortBernsteinPairing T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j f f).re≤
    -(3/350:ℝ)*shortVNorm T f^2 at hfinite
  simp only [Complex.sub_re] at hre
  change (circleShiftedBernsteinPairing T (circleExactSymmetricCoefficient T q p hq hp ψ) j f f).re≤0
  nlinarith only [hre,herror,hfinite,sq_nonneg (shortVNorm T f)]

end Lemniscate
