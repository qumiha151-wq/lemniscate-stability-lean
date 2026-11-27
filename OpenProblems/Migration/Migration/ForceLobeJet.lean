import Migration.RotatingHull

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Rotating.UnitLoop
variable {L : ℝ} (c : UnitLoop L)

/-- Real part conjugate to physical force in the moving tangent frame. -/
def forceCompanion (a b s : ℝ) : ℝ := a*(c.q 0 s-b*c.p 0 s)

theorem companion_hasDerivAt {a b : ℝ} (sol : c.IsRotating a b) (s : ℝ) :
    HasDerivAt (c.forceCompanion a b) (a-c.k s*c.F s) s := by
  apply (((c.qD 0 s).sub ((c.pD 0 s).const_mul b)).const_mul a).congr_deriv
  rw [sol s]; dsimp only [mixed]; ring

theorem force_hasDerivAt_companion {a b : ℝ} (sol : c.IsRotating a b) (s : ℝ) :
    HasDerivAt c.F (c.k s*c.forceCompanion a b s-a*b) s := by
  have eq : c.F = fun t => -a*(c.p 0 t+b*c.q 0 t) := funext sol
  rw [eq]
  apply (((c.pD 0 s).add ((c.qD 0 s).const_mul b)).const_mul (-a)).congr_deriv
  dsimp only [forceCompanion]; ring

theorem companion_eq_actual_jet {a b s : ℝ} (sol : c.IsRotating a b) (hk : c.k s≠0) :
    c.forceCompanion a b s = (deriv c.F s+a*b)/c.k s := by
  rw [(c.force_hasDerivAt_companion sol s).deriv]; field_simp; ring

theorem force_normal_height {a b s u v : ℝ} (sol : c.IsRotating a b)
    (nx : -deriv c.y s=u) (ny : deriv c.x s=v) :
    c.F s = -a*((u+b*v)*c.x s+(v-b*u)*c.y s) := by
  rw [sol s]
  simp only [mixed,p,q,normalSupport,tangentSupport,Pi.zero_apply,sub_zero]
  rw [ny,show deriv c.y s = -u by linarith]
  ring

/-- The scale-free signs of the two intrinsic radial coordinates determine
whether the true position is the similarity centre. -/
theorem force_pair_eq_zero_iff {a b s : ℝ} (ap : 0<a) (sol : c.IsRotating a b) :
    (c.forceCompanion a b s=0 ∧ c.F s=0) ↔ c.x s=0 ∧ c.y s=0 := by
  have den : 0<1+b^2 := by positivity
  have sq := c.unit s
  constructor
  · rintro ⟨hc,hf⟩; rw [sol s] at hf
    have hq : c.q 0 s-b*c.p 0 s=0 := (mul_eq_zero.mp hc).resolve_left ap.ne'
    have hp : c.p 0 s+b*c.q 0 s=0 := (mul_eq_zero.mp hf).resolve_left (neg_ne_zero.mpr ap.ne')
    have zeroQ : c.q 0 s=0 := by
      apply (mul_eq_zero.mp (show (1+b^2)*c.q 0 s=0 by linear_combination hq+b*hp)).resolve_left den.ne'
    have zeroP : c.p 0 s=0 := by simpa only [zeroQ,mul_zero,add_zero] using hp
    simp only [q,p,tangentSupport,normalSupport,Pi.zero_apply,sub_zero] at zeroQ zeroP
    constructor
    · linear_combination (deriv c.x s)*zeroQ-(deriv c.y s)*zeroP-c.x s*sq
    · linear_combination (deriv c.y s)*zeroQ+(deriv c.x s)*zeroP-c.y s*sq
  · rintro ⟨hx,hy⟩; rw [sol s]
    simp [forceCompanion,mixed,q,p,tangentSupport,normalSupport,hx,hy]

end MigrationGeometry.Rotating.UnitLoop

#print axioms MigrationGeometry.Rotating.UnitLoop.force_pair_eq_zero_iff
