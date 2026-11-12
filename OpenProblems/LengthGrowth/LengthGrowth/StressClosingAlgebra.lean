import LengthGrowth.StressNormalization

namespace LengthGrowth.StressAlgebra
noncomputable section

theorem normalized_closing_bound {E M D : ℝ} (hE : 0<E) (hM : 0<M)
    (_hD : 0≤D) (hclose : E/(2*M^2)≤16*Real.sqrt (2*E*D)/M^4) :
    1≤32*Real.sqrt 2*(Real.sqrt (E*D)/M^3)*(M/E) := by
  calc
    1 = (E/(2*M^2))*(2*M^2/E) := by field_simp [ne_of_gt hE,ne_of_gt hM]
    _ ≤ (16*Real.sqrt (2*E*D)/M^4)*(2*M^2/E) :=
      mul_le_mul_of_nonneg_right hclose (by positivity)
    _ = 32*Real.sqrt 2*(Real.sqrt (E*D)/M^3)*(M/E) := by
      rw [show 2*E*D=2*(E*D) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
      field_simp [ne_of_gt hE,ne_of_gt hM]
      ring

theorem energy_dissipation_of_ratio {E M D : ℝ} (hE : 0<E) (hM : 0<M)
    (hD : 0≤D) (hr : 1/4096<Real.sqrt (E*D)/M^3) :
    (1/16777216:ℝ)*M^6≤E*D := by
  have hsr : M^3/4096<Real.sqrt (E*D) := by
    have hh := (lt_div_iff₀ (pow_pos hM 3)).mp hr
    linarith
  have hsq := (sq_lt_sq₀ (by positivity : (0:ℝ)≤M^3/4096)
    (Real.sqrt_nonneg (E*D))).2 hsr
  rw [Real.sq_sqrt (mul_nonneg hE.le hD)] at hsq
  nlinarith

end
end LengthGrowth.StressAlgebra

#print axioms LengthGrowth.StressAlgebra.normalized_closing_bound
#print axioms LengthGrowth.StressAlgebra.energy_dissipation_of_ratio
