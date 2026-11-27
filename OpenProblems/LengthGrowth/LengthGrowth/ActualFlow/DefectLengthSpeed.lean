import LengthGrowth.ActualFlow.DefectAttraction

noncomputable section
namespace LengthGrowth.BendingSublevel

/-- The two instantaneous bounds survive averaging without controlling
higher curvature derivatives. A is length cubed times its physical rate;
Y is the normalized dissipation loss. -/
theorem speed_window {U A Y η : ℝ} (u1 : 1≤U) (yn : 0≤Y) (hp : 0<η)
    (vir : 2*Real.pi^2*U^2≤U*A+2*Y) (cs : A^2≤U*Y+(U^2/2)*A) :
    2*Real.pi^2*U-2*Y≤A ∧ A≤U^2/2+η+U*Y/(4*η) := by
  have up : 0<U := by linarith
  constructor
  · apply le_of_mul_le_mul_left (a:=U) _ up
    linarith only [vir,mul_le_mul_of_nonneg_right u1 yn]
  · have major : A≤U^2/2+Real.sqrt (U*Y) := by
      by_cases small : A≤U^2/2
      · linarith only [small,Real.sqrt_nonneg (U*Y)]
      · have large : 0≤A-U^2/2 := by linarith
        have sq : (A-U^2/2)^2≤U*Y := by
          nlinarith only [cs,mul_nonneg large (sq_nonneg U)]
        have bound := le_of_sq_le_sq (a:=A-U^2/2) (b:=Real.sqrt (U*Y))
          (by rwa [Real.sq_sqrt (mul_nonneg up.le yn)]) (Real.sqrt_nonneg _)
        linarith
    have y : Real.sqrt (U*Y)≤η+U*Y/(4*η) := by
      apply le_of_mul_le_mul_right (a:=4*η) _ (by positivity)
      rw [add_mul,div_mul_cancel₀ _ (by positivity)]
      nlinarith only [sq_nonneg (Real.sqrt (U*Y)-2*η),Real.sq_sqrt (mul_nonneg up.le yn)]
    linarith
end LengthGrowth.BendingSublevel

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem physical_speed_moments {s : ℝ} (hs : 0≤s) :
    let L := c.length s
    let E := c.energy s
    let D := c.dissipation s
    let J := c.lengthRate s
    let U := 2*c.normalizedProduct s
    let A := L^3*J
    let Y := L^4*(L*D-E*J)
    2*Real.pi^2*U^2≤U*A+2*Y ∧ A^2≤U*Y+(U^2/2)*A := by
  dsimp only [normalizedProduct]
  constructor
  · linarith only [mul_le_mul_of_nonneg_right (c.sharp_virial hs) (sq_nonneg (c.length s))]
  · linarith only [mul_le_mul_of_nonneg_right (c.lengthRate_sq_le hs) (show 0≤c.length s^6 by positivity)]

theorem physical_speed_window {s η : ℝ} (hs : 0≤s) (hp : 0<η)
    (decrease : 0≤c.length s*c.dissipation s-c.energy s*c.lengthRate s) :
    let U := 2*c.normalizedProduct s
    let A := c.length s^3*c.lengthRate s
    let Y := c.length s^4*(c.length s*c.dissipation s-c.energy s*c.lengthRate s)
    2*Real.pi^2*U-2*Y≤A ∧ A≤U^2/2+η+U*Y/(4*η) := by
  have u1 : 1≤2*c.normalizedProduct s := by
    have bound : 2*Real.pi^2≤c.normalizedProduct s := c.sharp_energy_length hs
    nlinarith only [bound,Real.pi_gt_three,sq_nonneg (Real.pi-3)]
  have inputs := c.physical_speed_moments hs
  exact BendingSublevel.speed_window u1 (mul_nonneg (pow_nonneg (c.length_pos hs).le _) decrease) hp inputs.1 inputs.2

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.physical_speed_window
