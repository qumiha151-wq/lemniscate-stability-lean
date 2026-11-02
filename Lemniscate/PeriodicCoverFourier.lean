import Lemniscate.PeriodicReflection

/-! Bloch components are obtained by taking Fourier indices M*n+j. The
construction uses normalized Haar L2 spaces, so the component map is a
contraction even when its source and target periods differ. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

def circleCoverIndex (M : ℕ) (j n : ℤ) : ℤ := (M:ℤ)*n+j

theorem circle_cover_index_injective (M : ℕ) (hM : 0 < M) (j : ℤ) :
    Function.Injective (circleCoverIndex M j) := by
  intro a b hab
  have hM0 : (M:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  exact mul_left_cancel₀ hM0 (add_right_cancel hab)

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

private theorem component_coefficients_mem_l2 (M : ℕ) (hM : 0 < M) (j : ℤ) (f : CircleL2 S) :
    Memℓp (fun n : ℤ => fourierCoeff f (circleCoverIndex M j n)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Function.comp_def] using
    (circle_fourier_square_summable S f).comp_injective (circle_cover_index_injective M hM j)

noncomputable def circleCoverComponentValue (M : ℕ) (hM : 0 < M) (j : ℤ)
    (f : CircleL2 S) : CircleL2 T :=
  (fourierBasis (T := T)).repr.symm
    ⟨fun n => fourierCoeff f (circleCoverIndex M j n),component_coefficients_mem_l2 S M hM j f⟩

theorem circle_cover_component_value_fourier (M : ℕ) (hM : 0 < M) (j : ℤ)
    (f : CircleL2 S) (n : ℤ) :
    fourierCoeff (circleCoverComponentValue T S M hM j f) n =
      fourierCoeff f (circleCoverIndex M j n) := by
  rw [← fourierBasis_repr]
  change ((fourierBasis (T := T)).repr ((fourierBasis (T := T)).repr.symm _)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]

private theorem component_value_norm_le (M : ℕ) (hM : 0 < M) (j : ℤ) (f : CircleL2 S) :
    ‖circleCoverComponentValue T S M hM j f‖ ≤ ‖f‖ := by
  have hsq : ‖circleCoverComponentValue T S M hM j f‖^2 ≤ ‖f‖^2 := by
    rw [circle_norm_sq_fourier,circle_norm_sq_fourier]
    simpa only [circle_cover_component_value_fourier,Function.comp_def] using
      tsum_comp_le_tsum_of_inj (circle_fourier_square_summable S f)
        (fun n => sq_nonneg ‖fourierCoeff f n‖) (circle_cover_index_injective M hM j)
  nlinarith [norm_nonneg (circleCoverComponentValue T S M hM j f),norm_nonneg f]

noncomputable def circleCoverComponent (M : ℕ) (hM : 0 < M) (j : ℤ) :
    CircleL2 S →L[ℂ] CircleL2 T :=
  LinearMap.mkContinuous
    { toFun := circleCoverComponentValue T S M hM j
      map_add' := by
        intro f g
        apply circle_fourier_ext T
        intro n
        simp only [circle_cover_component_value_fourier,circle_fourierCoeff_add]
      map_smul' := by
        intro c f
        apply circle_fourier_ext T
        intro n
        simp only [RingHom.id_apply,circle_cover_component_value_fourier,circle_fourierCoeff_smul] }
    1 (by
      intro f
      change ‖circleCoverComponentValue T S M hM j f‖ ≤ 1*‖f‖
      rw [one_mul]
      exact component_value_norm_le T S M hM j f)

theorem circle_cover_component_fourier (M : ℕ) (hM : 0 < M) (j : ℤ)
    (f : CircleL2 S) (n : ℤ) :
    fourierCoeff (circleCoverComponent T S M hM j f) n =
      fourierCoeff f (circleCoverIndex M j n) :=
  circle_cover_component_value_fourier T S M hM j f n

end Lemniscate
