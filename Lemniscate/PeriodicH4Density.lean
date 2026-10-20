import Lemniscate.PeriodicFormalAdjoint

/-! Density of the actual H4 domain in periodic L2 and uniqueness of an
adjoint image tested on that domain. Maximal-domain regularity is proved
separately in PeriodicAdjointRegularity. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_fourier_mem_h4 (n : ℤ) :
    (fourierBasis (T := T) n) ∈ circleH4Domain T := by
  change InCircleH4 T (fourierBasis (T := T) n)
  rw [← circle_continuous_l2_fourier_basis]
  exact circle_classical_mem_h4 T (fourier n)
    (circleFrequencyFactor T n • fourier n)
    ((circleFrequencyFactor T n)^2 • fourier n)
    ((circleFrequencyFactor T n)^3 • fourier n)
    ((circleFrequencyFactor T n)^4 • fourier n)
    (hasCircleDeriv_fourier T n) (by simpa only [pow_one] using circle_fourier_derivative_power T n 1)
    (circle_fourier_derivative_power T n 2) (circle_fourier_derivative_power T n 3)

theorem circle_h4_domain_dense : Dense (circleH4Domain T : Set (CircleL2 T)) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply le_antisymm le_top
  rw [← (fourierBasis (T := T)).dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro x ⟨n, rfl⟩
  exact circle_fourier_mem_h4 T n

theorem circle_h4_pairing_separates (g k : CircleL2 T)
    (h : ∀ f : circleH4Domain T, inner ℂ (f : CircleL2 T) g = inner ℂ (f : CircleL2 T) k) :
    g = k := by
  apply circle_fourier_ext T
  intro n
  rw [← fourierBasis_repr, ← fourierBasis_repr, HilbertBasis.repr_apply_apply,
    HilbertBasis.repr_apply_apply]
  exact h ⟨fourierBasis (T := T) n, circle_fourier_mem_h4 T n⟩

end Lemniscate
