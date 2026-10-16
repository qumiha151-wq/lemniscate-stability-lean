import Lemniscate.EvenCosineFamily
import Mathlib.Analysis.Fourier.AddCircle

/-! The cosine sequence space is embedded isometrically into actual periodic
L2 functions on the circle, using normalized Haar measure. The coefficient
energy is not yet identified with the geometric differential-operator form. -/
namespace Lemniscate
open Complex MeasureTheory
open CoarseArithmetic
open scoped ENNReal

noncomputable abbrev CircleL2 (T : ℝ) [Fact (0 < T)] :=
  Lp ℂ 2 (@AddCircle.haarAddCircle T _)

theorem h2_coefficients_mem_l2 (v : ℕ → ℂ) (hv : HasH2Coefficients v) : Memℓp v 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  simpa [Real.rpow_two] using h2_coefficients_mass_summable v hv

noncomputable def h2Sequence (v : ℕ → ℂ) (hv : HasH2Coefficients v) : CosineSequenceSpace :=
  ⟨v, h2_coefficients_mem_l2 v hv⟩

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleEvenCosineMode (j : ℕ) : CircleL2 T :=
  evenCosineMode (fourierBasis (T := T)) j

theorem circle_even_cosine_orthonormal : Orthonormal ℂ (circleEvenCosineMode T) :=
  even_cosine_orthonormal (fourierBasis (T := T)) (fourierBasis (T := T)).orthonormal

noncomputable def circleEvenCosineSynthesis : CosineSequenceSpace →ₗᵢ[ℂ] CircleL2 T :=
  evenCosineSynthesis (fourierBasis (T := T)) (fourierBasis (T := T)).orthonormal

theorem circle_even_cosine_hasSum (v : CosineSequenceSpace) :
    HasSum (fun j : ℕ => v j • circleEvenCosineMode T j) (circleEvenCosineSynthesis T v) :=
  even_cosine_hasSum (fourierBasis (T := T)) (fourierBasis (T := T)).orthonormal v

theorem circle_even_cosine_norm_sq (v : CosineSequenceSpace) :
    ‖circleEvenCosineSynthesis T v‖^2 = ∑' j : ℕ, ‖v j‖^2 := by
  rw [(circleEvenCosineSynthesis T).norm_map]
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) v
  simpa [Real.rpow_two] using h

theorem circle_even_cosine_mode_coeff (j : ℕ) (n : ℤ) :
    fourierCoeff (circleEvenCosineMode T j) n =
      if j = 0 then (if n = 0 then 1 else 0)
      else evenCosineFactor*((if n = 2*(j:ℤ) then 1 else 0)+
        (if n = -(2*(j:ℤ)) then 1 else 0)) := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  have hg := orthonormal_iff_ite.mp (fourierBasis (T := T)).orthonormal
  by_cases hj : j = 0
  · subst j
    simp only [circleEvenCosineMode, evenCosineMode, if_pos rfl, ite_true, hg]
  · simp only [circleEvenCosineMode, evenCosineMode, if_neg hj,
      inner_smul_right, inner_add_right, hg]

theorem circle_even_cosine_energy_bound (v : CosineSequenceSpace)
    (hv : HasH2Coefficients (fun j => v j)) :
    cosineH2Form (fun j => v j) ≤ -(21/4:ℝ)*‖circleEvenCosineSynthesis T v‖^2 := by
  rw [circle_even_cosine_norm_sq]
  exact cosine_h2_form_dissipative _ hv

noncomputable def h2CircleFunction (v : ℕ → ℂ) (hv : HasH2Coefficients v) : CircleL2 T :=
  circleEvenCosineSynthesis T (h2Sequence v hv)

theorem h2_circle_function_energy_bound (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    cosineH2Form v ≤ -(21/4:ℝ)*‖h2CircleFunction T v hv‖^2 := by
  exact circle_even_cosine_energy_bound T (h2Sequence v hv) hv

end Lemniscate
