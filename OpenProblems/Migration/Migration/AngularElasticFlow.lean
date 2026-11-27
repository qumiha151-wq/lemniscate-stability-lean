import Migration.AngularReconstruction
import Migration.CurveKinematics

/-! The reconstructed Cartesian position and its actual arclength geometry.
The two anchor velocities at parameter zero determine the translational part
of the velocity in normalized time. Spatial conclusions allow arbitrary anchors. -/

noncomputable section
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false

namespace MigrationGeometry.AngularGauge.Chart

variable {I : Set ℝ} {P : ℝ} (c : Chart I P)

/-- The unit vector with argument given by the angular chart. -/
def direction (t x : ℝ) : ℂ :=
  (Real.cos (c.theta t x) : ℂ) + (Real.sin (c.theta t x) : ℂ) * Complex.I

/-- The two scalar projected primitives combined into a Cartesian position. -/
def planePosition (a b : ℝ → ℝ) (t x : ℝ) : ℂ :=
  (c.position 1 0 a t x : ℂ) + (c.position 0 1 b t x : ℂ) * Complex.I

theorem direction_norm (t x : ℝ) : ‖c.direction t x‖ = 1 := by
  simp only [direction, Complex.ofReal_cos, Complex.ofReal_sin, Complex.norm_cos_add_sin_mul_I]

theorem direction_space {t : ℝ} (ht : t ∈ I) (x : ℝ) :
    HasDerivAt (c.direction t) ((c.v t x : ℂ) * (Complex.I * c.direction t x)) x := by
  have d := c.theta_x t ht x
  apply (d.cos.ofReal_comp.add (d.sin.ofReal_comp.mul_const Complex.I)).congr_deriv
  simp only [direction, Complex.ofReal_mul, Complex.ofReal_neg]
  linear_combination (-(c.v t x : ℂ) * (Real.sin (c.theta t x) : ℂ)) * Complex.I_mul_I

variable (a b : ℝ → ℝ)

theorem planePosition_space {t : ℝ} (ht : t ∈ I) (x : ℝ) :
    HasDerivAt (c.planePosition a b t) ((c.rho t : ℂ) * c.direction t x) x := by
  apply ((c.position_space ht 1 0 x a).ofReal_comp.add
    ((c.position_space ht 0 1 x b).ofReal_comp.mul_const Complex.I)).congr_deriv
  simp only [slope, T, direction, one_mul, zero_mul, add_zero, zero_add, Complex.ofReal_mul]
  ring

theorem planePosition_speed {t : ℝ} (ht : t ∈ I) (x : ℝ) :
    Flow.speed (c.planePosition a b t) x = c.rho t := by
  rw [Flow.speed, (c.planePosition_space a b ht x).deriv, norm_mul,
    c.direction_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (c.rho_pos t ht)]

theorem planePosition_regular {t : ℝ} (ht : t ∈ I) (x : ℝ) :
    deriv (c.planePosition a b t) x ≠ 0 := by
  apply norm_pos_iff.mp
  change 0 < Flow.speed (c.planePosition a b t) x
  rw [c.planePosition_speed a b ht]
  exact c.rho_pos t ht

theorem planePosition_tangent {t : ℝ} (ht : t ∈ I) :
    Flow.tangent (c.planePosition a b t) = c.direction t := by
  funext x
  rw [Flow.tangent, Flow.arcDerivative, c.planePosition_speed a b ht,
    (c.planePosition_space a b ht x).deriv, Complex.real_smul, Complex.ofReal_inv,
    ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (c.rho_pos t ht).ne'), one_mul]

theorem planePosition_normal {t : ℝ} (ht : t ∈ I) (x : ℝ) :
    Flow.normal (c.planePosition a b t) x = Complex.I * c.direction t x := by
  rw [Flow.normal, c.planePosition_tangent a b ht]

theorem planePosition_curvature {t : ℝ} (ht : t ∈ I) :
    Flow.curvature (c.planePosition a b t) = fun x => c.v t x / c.rho t := by
  funext x
  rw [Flow.curvature, c.planePosition_speed a b ht, c.planePosition_tangent a b ht,
    (c.direction_space ht x).deriv]
  have hu : conj (c.direction t x) * c.direction t x = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, c.direction_norm]
    norm_num
  rw [show conj (c.direction t x) * ((c.v t x : ℂ) * (Complex.I * c.direction t x)) =
       ((c.v t x : ℂ) * Complex.I) * (conj (c.direction t x) * c.direction t x) by ring, hu]
  simp

theorem planePosition_curvatureGradient {t : ℝ} (ht : t ∈ I) :
    Flow.curvatureGradient (c.planePosition a b t) = fun x => c.w t x / c.rho t ^ 2 := by
  funext x
  rw [Flow.curvatureGradient, Flow.arcDerivative, c.planePosition_speed a b ht,
    c.planePosition_curvature a b ht, ((c.v_x t ht x).div_const (c.rho t)).deriv]
  simp only [smul_eq_mul]
  ring

theorem planePosition_curvatureSecond {t : ℝ} (ht : t ∈ I) (x : ℝ) :
    Flow.curvatureSecond (c.planePosition a b t) x =
      (c.f t x - c.v t x ^ 3 / 2) / c.rho t ^ 3 := by
  rw [Flow.curvatureSecond, Flow.arcDerivative, c.planePosition_speed a b ht,
    c.planePosition_curvatureGradient a b ht, ((c.w_x t ht x).div_const (c.rho t ^ 2)).deriv]
  simp only [smul_eq_mul]
  ring

theorem planePosition_force {t : ℝ} (ht : t ∈ I) (x : ℝ) :
    Flow.force (c.planePosition a b t) x = c.f t x / c.rho t ^ 3 := by
  rw [Flow.force, c.planePosition_curvatureSecond a b ht, c.planePosition_curvature a b ht]
  ring

/-- With the true velocity at the two anchor coordinates, the reconstructed
curve moves with tangential speed ρu and normal speed −ρ⁴F in chart time. -/
theorem planePosition_time {t : ℝ} (ht : t ∈ I) (x : ℝ)
    (ha : HasDerivAt a (c.velocity 1 0 t 0) t)
    (hb : HasDerivAt b (c.velocity 0 1 t 0) t) :
    HasDerivAt (fun s => c.planePosition a b s x)
      (((c.rho t * c.u t x : ℝ) : ℂ) * Flow.tangent (c.planePosition a b t) x -
       ((c.rho t ^ 4 * Flow.force (c.planePosition a b t) x : ℝ) : ℂ) *
         Flow.normal (c.planePosition a b t) x) t := by
  rw [c.planePosition_tangent a b ht, c.planePosition_normal a b ht,
    c.planePosition_force a b ht]
  rw [show c.rho t ^ 4 * (c.f t x / c.rho t ^ 3) = c.rho t * c.f t x by
    field_simp [(c.rho_pos t ht).ne']]
  apply ((c.position_time ht 1 0 x a ha).ofReal_comp.add
    ((c.position_time ht 0 1 x b hb).ofReal_comp.mul_const Complex.I)).congr_deriv
  simp only [velocity, T, N, direction, one_mul, zero_mul, add_zero, zero_add, neg_zero,
    neg_one_mul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_neg]
  linear_combination (c.rho t : ℂ) * (c.f t x : ℂ) * (Real.sin (c.theta t x) : ℂ) *
    Complex.I_mul_I

/-- Under the physical clock the normal velocity is the negative of the
intrinsic elastic force. The equiarclength labels retain a tangential drift. -/
theorem planePosition_physical_time {clock : ℝ → ℝ} {s : ℝ} (hs : clock s ∈ I) (x : ℝ)
    (hclock : HasDerivAt clock (c.rho (clock s) ^ 4)⁻¹ s)
    (ha : HasDerivAt a (c.velocity 1 0 (clock s) 0) (clock s))
    (hb : HasDerivAt b (c.velocity 0 1 (clock s) 0) (clock s)) :
    HasDerivAt (fun z => c.planePosition a b (clock z) x)
      (((c.u (clock s) x / c.rho (clock s) ^ 3 : ℝ) : ℂ) *
          Flow.tangent (c.planePosition a b (clock s)) x -
        ((Flow.force (c.planePosition a b (clock s)) x : ℝ) : ℂ) *
          Flow.normal (c.planePosition a b (clock s)) x) s := by
  apply ((c.planePosition_time a b hs x ha hb).scomp s hclock).congr_deriv
  have hρ := Complex.ofReal_ne_zero.mpr (c.rho_pos (clock s) hs).ne'
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_mul]
  field_simp [hρ]

end MigrationGeometry.AngularGauge.Chart

#print axioms MigrationGeometry.AngularGauge.Chart.planePosition_space
#print axioms MigrationGeometry.AngularGauge.Chart.planePosition_force
#print axioms MigrationGeometry.AngularGauge.Chart.planePosition_time
#print axioms MigrationGeometry.AngularGauge.Chart.planePosition_physical_time

