import Lemniscate.PeriodicAdjointSobolevError

/-! Homogeneity and the triangle inequality for the angular Sobolev sum norm
used in the paper's Fourier truncation errors. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_angular_h4_norm_nonneg (f : circleH4Domain T) :
    0 ≤ circleAngularH4Norm T f := by
  have hT : 0 < T := Fact.out
  unfold circleAngularH4Norm
  positivity

theorem circle_angular_h4_norm_smul (c : ℂ) (f : circleH4Domain T) :
    circleAngularH4Norm T (c • f) = ‖c‖*circleAngularH4Norm T f := by
  simp only [circleAngularH4Norm,circle_h4_jet_smul,CircleH4Jet.smul,
    Submodule.coe_smul_of_tower,norm_smul]
  ring

theorem circle_angular_h4_norm_add_le (f g : circleH4Domain T) :
    circleAngularH4Norm T (f+g) ≤ circleAngularH4Norm T f+circleAngularH4Norm T g := by
  let k : ℝ := (2*Real.pi/T)⁻¹
  have hT : 0 < T := Fact.out
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  simp only [circleAngularH4Norm,circle_h4_jet_add,CircleH4Jet.add,Submodule.coe_add]
  change ‖(f : CircleL2 T)+(g : CircleL2 T)‖+
    k*‖(circleH4Jet T f).first+(circleH4Jet T g).first‖+
    k^2*‖(circleH4Jet T f).second+(circleH4Jet T g).second‖+
    k^3*‖(circleH4Jet T f).third+(circleH4Jet T g).third‖+
    k^4*‖(circleH4Jet T f).fourth+(circleH4Jet T g).fourth‖ ≤ _
  have h0 := norm_add_le (f : CircleL2 T) (g : CircleL2 T)
  have h1 := mul_le_mul_of_nonneg_left
    (norm_add_le (circleH4Jet T f).first (circleH4Jet T g).first) hk
  have h2 := mul_le_mul_of_nonneg_left
    (norm_add_le (circleH4Jet T f).second (circleH4Jet T g).second) (pow_nonneg hk 2)
  have h3 := mul_le_mul_of_nonneg_left
    (norm_add_le (circleH4Jet T f).third (circleH4Jet T g).third) (pow_nonneg hk 3)
  have h4 := mul_le_mul_of_nonneg_left
    (norm_add_le (circleH4Jet T f).fourth (circleH4Jet T g).fourth) (pow_nonneg hk 4)
  change _ ≤ (‖(f : CircleL2 T)‖+k*‖(circleH4Jet T f).first‖+
    k^2*‖(circleH4Jet T f).second‖+k^3*‖(circleH4Jet T f).third‖+
    k^4*‖(circleH4Jet T f).fourth‖)+
    (‖(g : CircleL2 T)‖+k*‖(circleH4Jet T g).first‖+
    k^2*‖(circleH4Jet T g).second‖+k^3*‖(circleH4Jet T g).third‖+
    k^4*‖(circleH4Jet T g).fourth‖)
  linarith

end Lemniscate
