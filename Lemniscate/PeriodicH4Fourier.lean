import Lemniscate.PeriodicAdjointRegularity

/-! The full Fourier characterization of the actual periodic H4 domain.
Only the function and its fourth multiplier need to be in L2; the three
intermediate weak derivatives are constructed, not assumed. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

theorem circle_fourierCoeff_zero (n : ℤ) : fourierCoeff (0 : CircleL2 T) n = 0 := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply, inner_zero_right]

theorem circle_h4_fourth_fourier (f : circleH4Domain T) (n : ℤ) :
    fourierCoeff (circleH4Jet T f).fourth n =
      (circleFrequencyFactor T n)^4*fourierCoeff (f : CircleL2 T) n := by
  rw [fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hfourth,
    fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hthird,
    fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hsecond,
    fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hfirst]
  ring

theorem circle_h4_of_fourth_fourier (f g : CircleL2 T)
    (heq : ∀ n : ℤ, fourierCoeff g n =
      (circleFrequencyFactor T n)^4*fourierCoeff f n) :
    InCircleH4 T f := by
  have hf : InCircleH2 T f := by
    apply circle_h2_of_fourth_distribution T f 0 0 g
    intro n
    simp only [circle_fourierCoeff_zero, mul_zero, zero_add]
    exact (heq n).symm
  obtain ⟨f₁, f₂, hf₁, hf₂⟩ := hf
  have hs : HasWeakCircleSecond T f₂ g := by
    apply weak_circle_second_of_fourier
    intro n
    rw [← circle_frequency_factor_sq, heq,
      fourier_of_weak_circle_deriv T _ _ hf₂, fourier_of_weak_circle_deriv T _ _ hf₁]
    ring
  obtain ⟨f₃, hf₃, hf₄⟩ := (weak_circle_second_iff_deriv_chain T f₂ g).mp hs
  exact ⟨f₁, f₂, f₃, g, hf₁, hf₂, hf₃, hf₄⟩

theorem circle_h4_iff_fourth_coefficients (f : CircleL2 T) :
    InCircleH4 T f ↔
      Memℓp (fun n : ℤ => (circleFrequencyFactor T n)^4*fourierCoeff f n) 2 := by
  constructor
  · intro hf
    have heq : (fun n : ℤ => (circleFrequencyFactor T n)^4*fourierCoeff f n) =
        (fun n : ℤ => fourierCoeff (circleH4Jet T ⟨f, hf⟩).fourth n) := by
      funext n
      exact (circle_h4_fourth_fourier T ⟨f, hf⟩ n).symm
    rw [heq]
    exact circle_fourier_mem_l2 T _
  · intro hf
    let g : CircleL2 T := (fourierBasis (T := T)).repr.symm
      ⟨fun n : ℤ => (circleFrequencyFactor T n)^4*fourierCoeff f n, hf⟩
    apply circle_h4_of_fourth_fourier T f g
    intro n
    rw [← fourierBasis_repr]
    change ((fourierBasis (T := T)).repr ((fourierBasis (T := T)).repr.symm _)) n = _
    rw [LinearIsometryEquiv.apply_symm_apply]

end Lemniscate
