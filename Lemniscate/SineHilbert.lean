import Lemniscate.SineConstraint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The infinite-dimensional Cauchy--Schwarz step in the sine constraint.
Complex coefficients are included, as required for a spectral argument.
Identification of this coefficient space with geometric sine functions
and the rotation mode remains a separate obligation. -/
namespace Lemniscate.CoarseArithmetic
open scoped ENNReal

noncomputable abbrev SineTailSpace := lp (fun _ : ℕ => ℂ) 2

theorem sine_tail_mem_l2 :
    Memℓp (fun n : ℕ => (sineRatio thetaParameter nome (n+2) : ℂ)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  have hs := (sine_constraint_series_bound thetaParameter nome
    ((by norm_num [rlo] : (0:ℝ) < (rlo:ℝ)).trans_le actual_nome_theta_r_bounds.1)
    coarse_nome_bounds).1
  simpa [Real.rpow_two, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hs

noncomputable def sineTailVector : SineTailSpace :=
  ⟨fun n => (sineRatio thetaParameter nome (n+2) : ℂ), sine_tail_mem_l2⟩

theorem sine_tail_norm_sq : ‖sineTailVector‖^2 =
    ∑' n : ℕ, (sineRatio thetaParameter nome (n+2))^2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) sineTailVector
  simpa [Real.rpow_two, Complex.norm_real, Real.norm_eq_abs, sq_abs, sineTailVector] using h

theorem sine_tail_norm_bound : ‖sineTailVector‖ < (87/500:ℝ) := by
  have hs := theta_nome_sine_constraint_bound
  rw [← sine_tail_norm_sq] at hs
  nlinarith [norm_nonneg sineTailVector]

theorem sine_constraint_first_mode (u : ℂ) (v : SineTailSpace)
    (horth : u + inner ℂ sineTailVector v = 0) :
    ‖u‖ ≤ (87/500:ℝ)*‖v‖ := by
  have hu : u = -(inner ℂ sineTailVector v) := eq_neg_of_add_eq_zero_left horth
  rw [hu, norm_neg]
  exact (norm_inner_le_norm sineTailVector v).trans
    (mul_le_mul_of_nonneg_right sine_tail_norm_bound.le (norm_nonneg v))

theorem sine_constraint_mass_bound (u : ℂ) (v : SineTailSpace)
    (horth : u + inner ℂ sineTailVector v = 0) :
    ‖u‖^2+‖v‖^2 ≤ (1+(87/500:ℝ)^2)*‖v‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg u) (sine_constraint_first_mode u v horth) 2
  nlinarith

theorem sine_constraint_energy_bound (u : ℂ) (v : SineTailSpace) (energy : ℝ)
    (horth : u + inner ℂ sineTailVector v = 0)
    (he : energy ≤ -100*‖v‖^2+2*63*‖u‖*‖v‖) :
    energy ≤ -75*(‖u‖^2+‖v‖^2) := by
  have hfirst := sine_constraint_first_mode u v horth
  have hmass := sine_constraint_mass_bound u v horth
  have hcross := mul_le_mul_of_nonneg_right hfirst (norm_nonneg v)
  apply Lemniscate.constrained_sine_dissipation energy (‖v‖^2) (‖u‖^2+‖v‖^2)
    (sq_nonneg _) _ hmass
  nlinarith

end Lemniscate.CoarseArithmetic
