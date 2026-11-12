import SolitonClassification.SolitonDilation

/-! No closed pure translator, including the stationary case. The data are
actual periodic position coordinates and their unit tangent/Frenet derivatives.
Stress and support identities are derived; none is assumed. -/

namespace ClosedSimilarity
noncomputable section
open MeasureTheory Set

structure ClosedUnitFrenetCurve where
  period : ℝ
  period_pos : 0 < period
  x : ℝ → ℝ
  y : ℝ → ℝ
  tx : ℝ → ℝ
  ty : ℝ → ℝ
  k : ℝ → ℝ
  v : ℝ → ℝ
  w : ℝ → ℝ
  dx : ∀ s, HasDerivAt x (tx s) s
  dy : ∀ s, HasDerivAt y (ty s) s
  dtx : ∀ s, HasDerivAt tx (-k s*ty s) s
  dty : ∀ s, HasDerivAt ty (k s*tx s) s
  dk : ∀ s, HasDerivAt k (v s) s
  dv : ∀ s, HasDerivAt v (w s) s
  continuous_w : Continuous w
  unit : ∀ s, tx s^2+ty s^2=1
  periodic_x : Function.Periodic x period
  periodic_y : Function.Periodic y period
  periodic_tx : Function.Periodic tx period
  periodic_ty : Function.Periodic ty period
  periodic_k : Function.Periodic k period
  periodic_v : Function.Periodic v period

namespace ClosedUnitFrenetCurve
variable (c : ClosedUnitFrenetCurve)

def force (s : ℝ) : ℝ := c.w s+c.k s^3/2
def stressX (s : ℝ) : ℝ := c.k s^2/2*c.tx s-c.v s*c.ty s
def stressY (s : ℝ) : ℝ := c.k s^2/2*c.ty s+c.v s*c.tx s
def normalSupport (s : ℝ) : ℝ := -c.x s*c.ty s+c.y s*c.tx s
def tangentSupport (s : ℝ) : ℝ := c.x s*c.tx s+c.y s*c.ty s
def positionCurvature (s : ℝ) : ℝ :=
  deriv c.x s*deriv (deriv c.y) s-deriv c.y s*deriv (deriv c.x) s
def positionForce (s : ℝ) : ℝ :=
  deriv (deriv c.positionCurvature) s+c.positionCurvature s^3/2

theorem position_unit_speed (s : ℝ) : (deriv c.x s)^2+(deriv c.y s)^2=1 := by
  rw [(c.dx s).deriv, (c.dy s).deriv]
  exact c.unit s

theorem positionCurvature_eq : c.positionCurvature=c.k := by
  have hx : deriv c.x=c.tx := funext fun s => (c.dx s).deriv
  have hy : deriv c.y=c.ty := funext fun s => (c.dy s).deriv
  funext s
  dsimp [positionCurvature]
  rw [hx, hy, (c.dtx s).deriv, (c.dty s).deriv]
  linear_combination c.k s*(c.unit s)

theorem positionForce_eq : c.positionForce=c.force := by
  have hk : deriv c.k=c.v := funext fun s => (c.dk s).deriv
  funext s
  dsimp [positionForce, force]
  rw [c.positionCurvature_eq, hk, (c.dv s).deriv]

theorem continuous_k : Continuous c.k :=
  continuous_iff_continuousAt.mpr fun s => (c.dk s).continuousAt

theorem continuous_force : Continuous c.force :=
  c.continuous_w.add ((c.continuous_k.pow 3).div_const 2)

theorem stressX_hasDerivAt (s : ℝ) :
    HasDerivAt c.stressX (-c.force s*c.ty s) s := by
  convert ((((c.dk s).pow 2).div_const 2).mul (c.dtx s)).sub
    ((c.dv s).mul (c.dty s)) using 1 <;> first | rfl | dsimp [force]; ring

theorem stressY_hasDerivAt (s : ℝ) :
    HasDerivAt c.stressY (c.force s*c.tx s) s := by
  convert ((((c.dk s).pow 2).div_const 2).mul (c.dty s)).add
    ((c.dv s).mul (c.dtx s)) using 1 <;> first | rfl | dsimp [force]; ring

theorem normalSupport_hasDerivAt (s : ℝ) :
    HasDerivAt c.normalSupport (-c.k s*c.tangentSupport s) s := by
  convert ((c.dx s).neg.mul (c.dty s)).add ((c.dy s).mul (c.dtx s)) using 1
    <;> first | rfl | dsimp [tangentSupport]; ring

theorem tangentSupport_hasDerivAt (s : ℝ) :
    HasDerivAt c.tangentSupport (1+c.k s*c.normalSupport s) s := by
  convert ((c.dx s).mul (c.dtx s)).add ((c.dy s).mul (c.dty s)) using 1
    <;> first | rfl | dsimp [normalSupport]; nlinarith [c.unit s]

theorem periodic_stressX : Function.Periodic c.stressX c.period := by
  intro s
  simp only [stressX, c.periodic_k s, c.periodic_v s, c.periodic_tx s, c.periodic_ty s]

theorem periodic_stressY : Function.Periodic c.stressY c.period := by
  intro s
  simp only [stressY, c.periodic_k s, c.periodic_v s, c.periodic_tx s, c.periodic_ty s]

theorem periodic_normalSupport : Function.Periodic c.normalSupport c.period := by
  intro s
  simp only [normalSupport, c.periodic_x s, c.periodic_y s, c.periodic_tx s, c.periodic_ty s]

theorem periodic_tangentSupport : Function.Periodic c.tangentSupport c.period := by
  intro s
  simp only [tangentSupport, c.periodic_x s, c.periodic_y s, c.periodic_tx s, c.periodic_ty s]

/-- A periodic stationary frame would contradict the already proved
strict positivity of dilation for periodic support data. -/
theorem no_stationary (hzero : ∀ s, c.force s=0) : False := by
  let z : PeriodicSupportProfile 0 0 c.period := {
    k := c.k, v := c.v, p := c.normalSupport, q := c.tangentSupport
    dk := c.dk
    dv := fun s => by
      convert c.dv s using 1
      have h := hzero s
      dsimp [force] at h
      simp only [zero_mul, sub_zero]
      linarith
    dp := c.normalSupport_hasDerivAt
    dq := c.tangentSupport_hasDerivAt
    periodic_k := c.periodic_k
    periodic_v := c.periodic_v
    periodic_p := c.periodic_normalSupport
    periodic_q := c.periodic_tangentSupport }
  exact z.no_nonexpanding_periodic_profile c.period_pos (le_refl 0)

/-- The translator equation gives zero total squared elastic force, by
projecting the actual stress derivative on the constant translation vector. -/
theorem translator_force_square_integral_zero (vx vy : ℝ)
    (htrans : ∀ s, c.force s=vx*c.ty s-vy*c.tx s) :
    (∫ s in 0..c.period, c.force s^2)=0 := by
  let g : ℝ → ℝ := fun s => vx*c.stressX s+vy*c.stressY s
  have hg : ∀ s, HasDerivAt g (-c.force s^2) s := by
    intro s
    convert ((c.stressX_hasDerivAt s).const_mul vx).add
      ((c.stressY_hasDerivAt s).const_mul vy) using 1
      <;> first | rfl | (rw [htrans]; ring)
  have hper : g c.period=g 0 := by
    have hx := c.periodic_stressX 0
    have hy := c.periodic_stressY 0
    dsimp [g]
    simpa using congrArg₂ (fun x y => vx*x+vy*y) hx hy
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ uIcc 0 c.period) => hg s)
    ((c.continuous_force.pow 2).neg.intervalIntegrable 0 c.period)
  rw [hper, sub_self, intervalIntegral.integral_neg] at hi
  linarith

theorem translator_force_zero (vx vy : ℝ)
    (htrans : ∀ s, c.force s=vx*c.ty s-vy*c.tx s) : ∀ s, c.force s=0 := by
  have hperiodic : Function.Periodic c.force c.period := by
    intro s
    rw [htrans, htrans, c.periodic_ty s, c.periodic_tx s]
  have hinterval := continuous_nonneg_zero_of_integral_zero c.period_pos
    (c.continuous_force.pow 2) (fun s _ => sq_nonneg (c.force s))
    (c.translator_force_square_integral_zero vx vy htrans)
  intro s
  obtain ⟨t, ht, he⟩ := hperiodic.exists_mem_Ico₀ c.period_pos s
  rw [he]
  have hz := hinterval t ⟨ht.1, ht.2.le⟩
  change c.force t^2=0 at hz
  exact sq_eq_zero_iff.mp hz

/-- No actual closed unit-speed planar curve is a pure translator of free
elastic flow. The zero translation vector is included, so stationarity is
excluded as well. -/
theorem no_closed_translator (vx vy : ℝ)
    (htrans : ∀ s, c.force s=vx*c.ty s-vy*c.tx s) : False :=
  c.no_stationary (c.translator_force_zero vx vy htrans)

/-- The same exclusion with curvature and force computed directly from
the first through fourth derivatives of the actual position coordinates. -/
theorem no_closed_translator_position_force (vx vy : ℝ)
    (htrans : ∀ s, c.positionForce s=vx*c.ty s-vy*c.tx s) : False := by
  rw [c.positionForce_eq] at htrans
  exact c.no_closed_translator vx vy htrans

end ClosedUnitFrenetCurve
end
end ClosedSimilarity

#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.no_closed_translator
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.no_stationary

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "NoClosedTranslators audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"NoClosedTranslators audit passed: {checked} declarations; standard axioms only."
