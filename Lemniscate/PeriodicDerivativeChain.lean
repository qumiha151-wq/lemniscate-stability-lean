import Lemniscate.PeriodicWeakFirst

/-! A weak second derivative in L2 supplies the missing first derivative.
The construction uses the complete Fourier basis, not an assumption of
pointwise differentiability or a finite truncation. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ENNReal ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_fourier_square_summable (f : CircleL2 T) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖^2) := by
  have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mp
    (lp.memℓp ((fourierBasis (T := T)).repr f))
  simpa only [fourierBasis_repr, ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem norm_first_multiplier_bound (a b : ℂ) :
    ‖a*b‖^2 ≤ ‖b‖^2 + ‖a^2*b‖^2 := by
  simp only [norm_mul, norm_pow]
  nlinarith [sq_nonneg (‖a‖^2*‖b‖ - ‖b‖), sq_nonneg (‖a‖*‖b‖)]

theorem circle_first_coefficients_summable (f g : CircleL2 T)
    (hfg : HasWeakCircleSecond T f g) :
    Summable (fun n : ℤ => ‖circleFrequencyFactor T n * fourierCoeff f n‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
    ((circle_fourier_square_summable T f).add (circle_fourier_square_summable T g))
  intro n
  rw [fourier_of_weak_circle_second T f g hfg n, ← circle_frequency_factor_sq]
  exact norm_first_multiplier_bound _ _

theorem circle_first_coefficients_mem_l2 (f g : CircleL2 T)
    (hfg : HasWeakCircleSecond T f g) :
    Memℓp (fun n : ℤ => circleFrequencyFactor T n * fourierCoeff f n) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    circle_first_coefficients_summable T f g hfg

noncomputable def circleFirstFromSecond (f g : CircleL2 T)
    (hfg : HasWeakCircleSecond T f g) : CircleL2 T :=
  (fourierBasis (T := T)).repr.symm
    ⟨fun n : ℤ => circleFrequencyFactor T n * fourierCoeff f n,
      circle_first_coefficients_mem_l2 T f g hfg⟩

theorem circle_first_from_second_fourier (f g : CircleL2 T)
    (hfg : HasWeakCircleSecond T f g) (n : ℤ) :
    fourierCoeff (circleFirstFromSecond T f g hfg) n =
      circleFrequencyFactor T n * fourierCoeff f n := by
  rw [← fourierBasis_repr]
  change ((fourierBasis (T := T)).repr
    ((fourierBasis (T := T)).repr.symm _)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem circle_first_from_second_weak (f g : CircleL2 T)
    (hfg : HasWeakCircleSecond T f g) :
    HasWeakCircleDeriv T f (circleFirstFromSecond T f g hfg) :=
  weak_circle_deriv_of_fourier T _ _ (circle_first_from_second_fourier T f g hfg)

theorem circle_first_from_second_deriv (f g : CircleL2 T)
    (hfg : HasWeakCircleSecond T f g) :
    HasWeakCircleDeriv T (circleFirstFromSecond T f g hfg) g := by
  apply weak_circle_deriv_of_fourier
  intro n
  rw [fourier_of_weak_circle_second T f g hfg,
    circle_first_from_second_fourier, ← circle_frequency_factor_sq]
  ring

theorem weak_circle_second_iff_deriv_chain (f g : CircleL2 T) :
    HasWeakCircleSecond T f g ↔
      ∃ u : CircleL2 T, HasWeakCircleDeriv T f u ∧ HasWeakCircleDeriv T u g := by
  constructor
  · intro hfg
    exact ⟨circleFirstFromSecond T f g hfg, circle_first_from_second_weak T f g hfg,
      circle_first_from_second_deriv T f g hfg⟩
  · rintro ⟨u, hfu, hug⟩
    exact weak_circle_second_of_deriv_chain T f u g hfu hug

/-- Periodic H2 membership defined by two successive L2 weak derivatives. -/
def InCircleH2 (f : CircleL2 T) : Prop :=
  ∃ u g : CircleL2 T, HasWeakCircleDeriv T f u ∧ HasWeakCircleDeriv T u g

theorem circle_h2_iff_weak_second (f : CircleL2 T) :
    InCircleH2 T f ↔ ∃ g : CircleL2 T, HasWeakCircleSecond T f g := by
  constructor
  · rintro ⟨u, g, hfu, hug⟩
    exact ⟨g, weak_circle_second_of_deriv_chain T f u g hfu hug⟩
  · rintro ⟨g, hfg⟩
    obtain ⟨u, hfu, hug⟩ := (weak_circle_second_iff_deriv_chain T f g).mp hfg
    exact ⟨u, g, hfu, hug⟩

noncomputable def h2CircleFirst (v : ℕ → ℂ) (hv : HasH2Coefficients v) : CircleL2 T :=
  circleFirstFromSecond T (h2CircleFunction T v hv) (h2CircleSecond T v hv)
    (h2_circle_second_weak T v hv)

theorem h2_circle_derivative_chain (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    HasWeakCircleDeriv T (h2CircleFunction T v hv) (h2CircleFirst T v hv) ∧
    HasWeakCircleDeriv T (h2CircleFirst T v hv) (h2CircleSecond T v hv) :=
  ⟨circle_first_from_second_weak T _ _ (h2_circle_second_weak T v hv),
    circle_first_from_second_deriv T _ _ (h2_circle_second_weak T v hv)⟩

theorem h2_circle_function_mem_h2 (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    InCircleH2 T (h2CircleFunction T v hv) :=
  ⟨h2CircleFirst T v hv, h2CircleSecond T v hv, h2_circle_derivative_chain T v hv⟩

end Lemniscate
