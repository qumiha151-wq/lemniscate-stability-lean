import Lemniscate.PeriodicCoverExtension
import Lemniscate.PeriodicCoverRotation

/-! The rotational kernel, its semisimplicity and the nonzero spectral bound
on the naturally extended profile. Only the original period's profile and
Fourier identities are hypotheses. -/
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
include hq hp he hqreal hpreal hs hc ho hr

theorem paper_periodic_cover_spectrum (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) :
    let E := circlePeriodicExtension T S M hS
    let Q := E q
    let P := E p
    let A := circleH4Operator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))
    ∃ R : circleH4Domain S,
      (R:CircleL2 S) = circleContinuousL2 S (Q*P) ∧
      (R:CircleL2 S) ≠ 0 ∧
      LinearMap.ker A = Submodule.span ℂ {R} ∧
      (∀ f g : circleH4Domain S, A f = (g:CircleL2 S) → A g = 0 → A f = 0) ∧
      (∀ w : ℂ, w ≠ 0 →
        w ∈ circleSpectrum S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) →
        w.re ≤ if M = 1 then -(21/4:ℝ) else -(1/(2*(M:ℝ)^2))) := by
  let E := circlePeriodicExtension T S M hS
  let Q := E q
  let P := E p
  have hQ : HasCircleDeriv S Q P := circle_periodic_extension_deriv T S M hS q p hq
  have hP : HasCircleDeriv S P (-(Q^3)) := by
    simpa only [Q,map_neg,map_pow] using circle_periodic_extension_deriv T S M hS _ _ hp
  have hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1 := fun x => he (circleCoverProjection T S M hS x)
  have hMZ : (M:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hmulti (n : ℤ) : fourierCoeff (Q^2 : C(AddCircle S, ℂ)) ((M:ℤ)*n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n := by
    have h := circle_periodic_extension_fourier T S M hM hS (q^2) ((M:ℤ)*n)
    simpa [E,Q,map_pow,Int.mul_ediv_cancel_left _ hMZ] using h
  have hvanish (n : ℤ) (hn : ¬(M:ℤ) ∣ n) :
      fourierCoeff (Q^2 : C(AddCircle S, ℂ)) n = 0 := by
    have h := circle_periodic_extension_fourier T S M hM hS (q^2) n
    simpa only [if_neg hn,map_pow] using h
  let R := circleRotationH4 S Q P hQ hP
  refine ⟨R,rfl,?_,?_,?_,?_⟩
  · exact paper_cover_rotation_ne_zero T S q p hq hs hc ho M hM hS Q P hQ hmulti
  · exact paper_cover_kernel T S q p hq hp he hqreal hpreal hs hc ho hr
      M hM hS Q P hQ hP hE hmulti hvanish
  · exact paper_cover_no_generalized_kernel T S q p hq hp he hqreal hpreal hs hc ho hr
      M hM hS _ _ _ (circle_profile_square_deriv S Q P hQ)
      (circle_profile_square_second S Q P hQ hP hE) hmulti hvanish
  · exact paper_cover_nonzero_spectral_bound T S q p hq hp he hqreal hpreal hs hc ho hr
      M hM hS _ _ _ (circle_profile_square_deriv S Q P hQ)
      (circle_profile_square_second S Q P hQ hP hE) hmulti hvanish

end Profile
end Lemniscate
