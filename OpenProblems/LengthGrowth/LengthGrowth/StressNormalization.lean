import LengthGrowth.StressAlgebra
import Mathlib.Tactic.FieldSimp

/-! Pure algebra connecting actual integral bounds to the normalized
stress constants. The hypotheses must be proved for the curve separately. -/
namespace LengthGrowth.StressAlgebra
noncomputable section
set_option maxHeartbeats 2000000

theorem normalized_pointwise_bound {E M D B : ℝ}
    (hE : 0<E) (hM : 0<M) (_hD : 0≤D) (_hB : 0≤B)
    (hpoint : M^2≤4*E^2+2*Real.sqrt (2*E)*B)
    (hgradient : B^2≤E*M^2+Real.sqrt (2*E*D)) :
    (M/E)^2≤4+2*Real.sqrt 2*
      Real.sqrt ((M/E)^2+Real.sqrt 2*(Real.sqrt (E*D)/M^3)*(M/E)^3) := by
  let z := (M/E)^2+Real.sqrt 2*(Real.sqrt (E*D)/M^3)*(M/E)^3
  have hz0 : 0≤z := by dsimp [z]; positivity
  have hznorm : E^3*z=E*M^2+Real.sqrt 2*Real.sqrt (E*D) := by
    dsimp [z]
    field_simp [ne_of_gt hE,ne_of_gt hM]
  have hBsq : B^2≤E^3*z := by
    rw [hznorm]
    simpa only [show 2*E*D=2*(E*D) by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] using hgradient
  have hscale : B≤E*Real.sqrt E*Real.sqrt z := by
    apply le_of_sq_le_sq _ (by positivity)
    have he : (E*Real.sqrt E*Real.sqrt z)^2=E^3*z := by
      calc
        _ = E^2*(Real.sqrt E)^2*(Real.sqrt z)^2 := by ring
        _ = E^3*z := by rw [Real.sq_sqrt hE.le,Real.sq_sqrt hz0]; ring
    rwa [he]
  have hmul := mul_le_mul_of_nonneg_left hscale
    (show 0≤2*Real.sqrt 2*Real.sqrt E by positivity)
  have he : 2*Real.sqrt 2*Real.sqrt E*(E*Real.sqrt E*Real.sqrt z)=
      E^2*(2*Real.sqrt 2*Real.sqrt z) := by
    calc
      _ = 2*Real.sqrt 2*E*(Real.sqrt E)^2*Real.sqrt z := by ring
      _ = E^2*(2*Real.sqrt 2*Real.sqrt z) := by rw [Real.sq_sqrt hE.le]; ring
  rw [he] at hmul
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at hpoint
  have htotal : M^2≤(4+2*Real.sqrt 2*Real.sqrt z)*E^2 := by nlinarith
  change (M/E)^2≤4+2*Real.sqrt 2*Real.sqrt z
  rw [div_pow]
  exact (div_le_iff₀ (sq_pos_of_pos hE)).2 htotal

theorem stress_variation_normalized {E M D B : ℝ}
    (hE : 0≤E) (hM : 0<M) (_hD : 0≤D)
    (hB : B≤2*Real.sqrt E*M) :
    2*B*Real.sqrt D≤4*(Real.sqrt (E*D)/M^3)*M^4 := by
  calc
    2*B*Real.sqrt D = B*(2*Real.sqrt D) := by ring
    _ ≤ (2*Real.sqrt E*M)*(2*Real.sqrt D) :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    _ = 4*Real.sqrt (E*D)*M := by rw [Real.sqrt_mul hE]; ring
    _ = 4*(Real.sqrt (E*D)/M^3)*M^4 := by
      field_simp [ne_of_gt hM]

end
end LengthGrowth.StressAlgebra

#print axioms LengthGrowth.StressAlgebra.normalized_pointwise_bound
#print axioms LengthGrowth.StressAlgebra.stress_variation_normalized

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`LengthGrowth.StressAlgebra.normalized_pointwise_bound,
      `LengthGrowth.StressAlgebra.stress_variation_normalized] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "Stress normalization audit failed: {name} depends on {axiomName}"
  logInfo "Stress normalization audit passed for 2 declarations."
