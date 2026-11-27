import Migration.SingularEndpointAction

noncomputable section
namespace MigrationGeometry.AngularExcursion

/-- The three arclength derivatives of the horizontal tangent in the
actual Frenet system. The scalar variables Y and z are h_s and x_s. -/
theorem horizontal_third {Y z k p q : ℝ→ℝ}
    (dy : ∀s,HasDerivAt Y (k s*z s) s) (dz : ∀s,HasDerivAt z (-k s*Y s) s)
    (dk : ∀s,HasDerivAt k (p s) s) (dp : ∀s,HasDerivAt p (q s) s)
    (s : ℝ) : deriv (deriv (deriv z)) s=Y s*(k s)^3-3*z s*k s*p s-Y s*q s := by
  have z1 : deriv z = fun r=> -k r*Y r := funext fun r=>(dz r).deriv
  have z2d (r : ℝ) : HasDerivAt (deriv z) (-p r*Y r-(k r)^2*z r) r := by
    rw [z1]; apply ((dk r).neg.mul (dy r)).congr_deriv
    dsimp; ring
  have z2 : deriv (deriv z)=fun r=> -p r*Y r-(k r)^2*z r := funext fun r=>(z2d r).deriv
  rw [z2]
  apply HasDerivAt.deriv
  apply (((dp s).neg.mul (dy s)).sub (((dk s).pow 2).mul (dz s))).congr_deriv
  dsimp; ring

def jumpSign (x : ℝ) : ℝ := if x<0 then -1 else if 0<x then 1 else 0

/-- The right-going orientation of a zero determines its net tip boundary
term. At a cubic zero, the Frenet value of z_sss forces a positive |F|
coefficient; at a simple zero, the coefficient is sign(k) F. -/
theorem simple_tip_coefficient {Y k F d : ℝ} (unit : Y=1 ∨ Y = -1) (dk : k≠0)
    (slope : d= -Y*k) : -(jumpSign d)*F*Y=jumpSign k*F := by
  subst d
  rcases unit with rfl|rfl <;> rcases lt_or_gt_of_ne dk with h|h <;>
    simp [jumpSign,h,not_lt_of_gt h]

theorem cubic_tip_coefficient {Y F d : ℝ} (unit : Y=1 ∨ Y= -1) (force : F≠0)
    (third : d= -Y*F) : -(jumpSign d)*F*Y=|F| := by
  rw [simple_tip_coefficient unit force third]
  rcases lt_or_gt_of_ne force with h|h
  · simp [jumpSign,h,abs_of_neg h]
  · simp [jumpSign,h,h.not_gt,abs_of_pos h]

end MigrationGeometry.AngularExcursion
#print axioms MigrationGeometry.AngularExcursion.horizontal_third
#print axioms MigrationGeometry.AngularExcursion.cubic_tip_coefficient
