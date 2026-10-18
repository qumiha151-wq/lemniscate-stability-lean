import Lemniscate.PeriodicCosineH2

/-! Fourier coefficient linearity and multiplication by a Fourier mode.
These identities are for actual continuous functions on the circle. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFourierCLM (n : ℤ) : C(AddCircle T, ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ (fourierBasis (T := T) n)).comp
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)

theorem circle_fourier_clm_apply (n : ℤ) (f : C(AddCircle T, ℂ)) :
    circleFourierCLM T n f = fourierCoeff f n := by
  change inner ℂ (fourierBasis (T := T) n) (circleContinuousL2 T f) = _
  rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr, circle_continuous_l2_fourier]

theorem circle_continuous_fourier_add (f g : C(AddCircle T, ℂ)) (n : ℤ) :
    fourierCoeff (f+g) n = fourierCoeff f n + fourierCoeff g n := by
  simpa only [circle_fourier_clm_apply] using (circleFourierCLM T n).map_add f g

theorem circle_continuous_fourier_sub (f g : C(AddCircle T, ℂ)) (n : ℤ) :
    fourierCoeff (f-g) n = fourierCoeff f n - fourierCoeff g n := by
  simpa only [circle_fourier_clm_apply] using (circleFourierCLM T n).map_sub f g

theorem circle_continuous_fourier_smul (c : ℂ) (f : C(AddCircle T, ℂ)) (n : ℤ) :
    fourierCoeff (c • f) n = c * fourierCoeff f n := by
  simpa only [circle_fourier_clm_apply, smul_eq_mul] using
    (circleFourierCLM T n).map_smul c f

theorem circle_continuous_fourier_one (n : ℤ) :
    fourierCoeff (1 : C(AddCircle T, ℂ)) n = if n = 0 then 1 else 0 := by
  have he : (1 : C(AddCircle T, ℂ)) = fourier 0 := by
    ext x
    simp
  rw [he, fourierCoeff_fourier]
  simp [Pi.single_apply, eq_comm]

theorem circle_continuous_fourier_mode (n m : ℤ) :
    fourierCoeff (fourier m : C(AddCircle T, ℂ)) n = if n = m then 1 else 0 := by
  rw [fourierCoeff_fourier]
  simp [Pi.single_apply, eq_comm]

theorem circle_fourier_product_mode (h : C(AddCircle T, ℂ)) (n m : ℤ) :
    fourierCoeff (h * fourier m : C(AddCircle T, ℂ)) n = fourierCoeff h (n-m) := by
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards [] with x
  change fourier (-n) x * (h x * fourier m x) = fourier (-(n-m)) x * h x
  calc
    _ = (fourier (-n) x * fourier m x) * h x := by ring
    _ = fourier (-n+m) x * h x := by rw [← fourier_add]
    _ = _ := by rw [show -n+m = -(n-m) by omega]

theorem circle_fourier_product_smul_mode (h : C(AddCircle T, ℂ)) (c : ℂ) (n m : ℤ) :
    fourierCoeff (h * (c • fourier m) : C(AddCircle T, ℂ)) n = c * fourierCoeff h (n-m) := by
  have he : h * (c • fourier (T := T) m) = c • (h * fourier (T := T) m) := by
    ext x
    change h x * (c*fourier m x) = c*(h x*fourier m x)
    ring
  rw [he, circle_continuous_fourier_smul, circle_fourier_product_mode]

end Lemniscate
