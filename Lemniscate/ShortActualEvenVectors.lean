import Lemniscate.ShortEvenFunctions
import Lemniscate.ShortNeutralComparison

/-! The actual neutral vectors, restricted to the even Fourier domain.
This lets Hilbert-space form estimates use precisely their valid domain. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

noncomputable def shortEvenVSeminorm : Seminorm ℂ (shortEvenDomain T) :=
  (shortVSeminorm T).comp (shortEvenDomain T).subtype

noncomputable def shortEvenH1Seminorm : Seminorm ℂ (shortEvenDomain T) :=
  (shortH1Seminorm T).comp (shortEvenDomain T).subtype

theorem short_even_v_apply (f : shortEvenDomain T) :
    shortEvenVSeminorm T f = shortVNorm T (f:circleH4Domain T) := rfl

theorem short_even_h1_apply (f : shortEvenDomain T) :
    shortEvenH1Seminorm T f = shortH1Norm T (f:circleH4Domain T) := rfl

theorem short_even_norm (f : shortEvenDomain T) :
    ‖f‖ = ‖((f:circleH4Domain T):CircleL2 T)‖ := rfl

theorem short_actual_neutral_vectors_mem_even
    (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (ψ : circleH4Domain T) (hψ : InCircleEvenSineSector T (ψ:CircleL2 T)) :
    circleShortRotationVector T q p hq hp ∈ shortEvenDomain T ∧
      circleShortAdjointVector T ψ ∈ shortEvenDomain T := by
  constructor
  · intro n hn
    rcases hn with ⟨k,hk⟩
    have hnk : n = 2*k+1 := by omega
    rw [hnk]
    change fourierCoeff ((-I) • circleUnitRotation T q p) (2*k+1) = 0
    rw [circle_fourierCoeff_smul,circle_unit_rotation_no_odd T q p hq ho,mul_zero]
  · intro n hn
    rcases hn with ⟨k,hk⟩
    have hnk : n = 2*k+1 := by omega
    rw [hnk]
    change fourierCoeff ((-I) • (ψ:CircleL2 T)) (2*k+1) = 0
    rw [circle_fourierCoeff_smul,hψ.2,mul_zero]

theorem short_even_householder_coe (e a f : shortEvenDomain T) :
    ((neutralHouseholder e a f:shortEvenDomain T):circleH4Domain T) =
      neutralHouseholderDomain (e:circleH4Domain T) (a:circleH4Domain T)
        (f:circleH4Domain T) := by
  rw [neutral_householder_apply]
  rfl

theorem short_even_right_coe (e ψ f : shortEvenDomain T) :
    (shortRightInput e ψ f:circleH4Domain T) =
      shortRightInput (e:circleH4Domain T) (ψ:circleH4Domain T) (f:circleH4Domain T) := rfl

theorem short_even_left_coe (e ψ f : shortEvenDomain T) :
    (shortLeftInput e ψ f:circleH4Domain T) =
      shortLeftInput (e:circleH4Domain T) (ψ:circleH4Domain T) (f:circleH4Domain T) := rfl

end Lemniscate
