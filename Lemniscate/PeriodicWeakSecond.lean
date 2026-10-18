import Lemniscate.PeriodicClassicalFourier

/-! The second frequency multiplier is identified with a weak second derivative
by testing against every twice continuously differentiable periodic function.
This is an integration-by-parts statement in the actual L2 space. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleContinuousL2 (f : C(AddCircle T, ℂ)) : CircleL2 T :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f

theorem circle_continuous_l2_fourier (f : C(AddCircle T, ℂ)) (n : ℤ) :
    fourierCoeff (circleContinuousL2 T f) n = fourierCoeff f n :=
  fourierCoeff_toLp f n

theorem circle_fourierCoeff_smul (c : ℂ) (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (c • f) n = c * fourierCoeff f n := by
  simp only [← fourierBasis_repr, HilbertBasis.repr_apply_apply, inner_smul_right]

theorem circle_inner_continuous_integral (f : CircleL2 T) (φ : C(AddCircle T, ℂ)) :
    inner ℂ f (circleContinuousL2 T φ) =
      ∫ x : AddCircle T, conj (f x) * φ x ∂AddCircle.haarAddCircle := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) φ]
    with x hx
  change inner ℂ (f x) ((circleContinuousL2 T φ) x) = conj (f x)*φ x
  change inner ℂ (f x) ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ φ) x) = _
  rw [hx]
  simp only [RCLike.inner_apply', mul_comm]

theorem circle_real_multiplier_duality (f g u v : CircleL2 T) (m : ℤ → ℝ)
    (hfg : ∀ n, fourierCoeff g n = (m n:ℂ)*fourierCoeff f n)
    (huv : ∀ n, fourierCoeff v n = (m n:ℂ)*fourierCoeff u n) :
    inner ℂ g u = inner ℂ f v := by
  rw [← (fourierBasis (T := T)).repr.inner_map_map g u,
    ← (fourierBasis (T := T)).repr.inner_map_map f v,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply', fourierBasis_repr, hfg n, huv n,
    map_mul, Complex.conj_ofReal]
  ring

/-- Weak second derivative in the real coordinate of the circle: the complex
L2 pairing satisfies integration by parts against all periodic C2 test functions.
The test function and both of its classical derivatives are bundled as continuous maps. -/
def HasWeakCircleSecond (f g : CircleL2 T) : Prop :=
  ∀ (φ φ₁ φ₂ : C(AddCircle T, ℂ)), HasCircleDeriv T φ φ₁ → HasCircleDeriv T φ₁ φ₂ →
    inner ℂ g (circleContinuousL2 T φ) = inner ℂ f (circleContinuousL2 T φ₂)

theorem weak_circle_second_of_fourier (f g : CircleL2 T)
    (hfg : ∀ n : ℤ, fourierCoeff g n =
      ((-((2*Real.pi/T)^2*(n:ℝ)^2):ℝ):ℂ)*fourierCoeff f n) :
    HasWeakCircleSecond T f g := by
  intro φ φ₁ φ₂ h₁ h₂
  apply circle_real_multiplier_duality T f g (circleContinuousL2 T φ)
    (circleContinuousL2 T φ₂) (fun n : ℤ => -((2*Real.pi/T)^2*(n:ℝ)^2)) hfg
  intro n
  simpa only [circle_continuous_l2_fourier] using
    fourierCoeff_classical_second T φ φ₁ φ₂ h₁ h₂ n

noncomputable def h2CircleSecond (v : ℕ → ℂ) (hv : HasH2Coefficients v) : CircleL2 T :=
  ((((2*Real.pi/T)^2:ℝ):ℂ)) • h2CircleAngularSecond T v hv

theorem h2_circle_second_fourier (v : ℕ → ℂ) (hv : HasH2Coefficients v) (n : ℤ) :
    fourierCoeff (h2CircleSecond T v hv) n =
      ((-((2*Real.pi/T)^2*(n:ℝ)^2):ℝ):ℂ)*fourierCoeff (h2CircleFunction T v hv) n := by
  rw [h2CircleSecond, circle_fourierCoeff_smul, h2_circle_angular_second_fourier]
  push_cast
  ring

theorem h2_circle_second_weak (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    HasWeakCircleSecond T (h2CircleFunction T v hv) (h2CircleSecond T v hv) :=
  weak_circle_second_of_fourier T _ _ (h2_circle_second_fourier T v hv)

theorem h2_circle_second_integration_by_parts (v : ℕ → ℂ) (hv : HasH2Coefficients v)
    (φ φ₁ φ₂ : C(AddCircle T, ℂ)) (h₁ : HasCircleDeriv T φ φ₁)
    (h₂ : HasCircleDeriv T φ₁ φ₂) :
    (∫ x : AddCircle T, conj (h2CircleSecond T v hv x)*φ x ∂AddCircle.haarAddCircle) =
      ∫ x : AddCircle T, conj (h2CircleFunction T v hv x)*φ₂ x ∂AddCircle.haarAddCircle := by
  simpa only [circle_inner_continuous_integral] using
    h2_circle_second_weak T v hv φ φ₁ φ₂ h₁ h₂

end Lemniscate
