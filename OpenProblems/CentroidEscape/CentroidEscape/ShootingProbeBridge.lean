import CentroidEscape.OrderMetricGrid
import CentroidEscape.ShootingDomain

/-!
# Probe grids, a common shooting horizon, and unweighted output balls

Each probe may use its own positive terminal time and step size. Uniqueness
transfers its endpoint to the common longer-horizon shooting map. Projection
scales the weighted output radii by1,4,64; the state allowance1e-43 is therefore
not silently reused as an unweighted shooting-output allowance.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

def projectBallVector (b : BallVector) : Fin 3 → RationalBall :=
  ![b 1,(RationalBall.point 4).mul (b 2),(RationalBall.point 64).mul (b 5)]

def projectedBallCenter (b : BallVector) : Fin 3 → ℝ :=
  fun i=>((projectBallVector b i).center:ℝ)

theorem projectBallVector_contains {b : BallVector} {z : WeightedState}
    (hb : ∀ i, (b i).Contains (z i)) :
    ∀ i, (projectBallVector b i).Contains (shootingProjection z i) := by
  intro i
  fin_cases i
  · exact hb 1
  · change ((RationalBall.point 4).mul (b 2)).Contains (4*z 2)
    simpa only [Rat.cast_ofNat] using
      RationalBall.contains_mul (RationalBall.contains_point 4) (hb 2)
  · change ((RationalBall.point 64).mul (b 5)).Contains (64*z 5)
    simpa only [Rat.cast_ofNat] using
      RationalBall.contains_mul (RationalBall.contains_point 64) (hb 5)

theorem projectedBallCenter_error {b : BallVector} {z : WeightedState} {η : ℚ}
    (hη : 0≤η) (hb : ∀ i, (b i).Contains (z i))
    (hrad : ∀ i, (projectBallVector b i).radius≤η) :
    ‖projectedBallCenter b-shootingProjection z‖≤(η:ℝ) := by
  rw [pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr hη)]
  intro i
  have hc := projectBallVector_contains hb i
  have hr : ((projectBallVector b i).radius:ℝ)≤(η:ℝ) := Rat.cast_le.mpr (hrad i)
  change |((projectBallVector b i).center:ℝ)-shootingProjection z i|≤(η:ℝ)
  rw [abs_sub_comm]
  exact hc.trans hr

lemma projectBallVector_radii (b : BallVector) :
    (projectBallVector b 0).radius=(b 1).radius ∧
    (projectBallVector b 1).radius=4*(b 2).radius ∧
    (projectBallVector b 2).radius=64*(b 5).radius := by
  change (b 1).radius=(b 1).radius ∧
    ((RationalBall.point 4).mul (b 2)).radius=4*(b 2).radius ∧
    ((RationalBall.point 64).mul (b 5)).radius=64*(b 5).radius
  norm_num [RationalBall.mul,RationalBall.point]

def order60EndpointBalls (S N : ℕ) (st : ℕ → FixedTaylorState) : BallVector :=
  fun i=>(((st N).coefficient 0 i).toRational S).inflate (1/10^43)

/-- Transfer each probe's independently checked endpoint to a common U. -/
theorem checked_order60_probe_endpoint {S N : ℕ} (hS : 0<S) (hN : 0<N) (hNmax : N≤750)
    {h : ℚ} (hh : 0≤h) (hhmax : h≤1/100)
    (st : ℕ → FixedTaylorState)
    (hcheck : ∀ j<N, checkOrderTaylorData S 60 (st j)=true)
    (hglue : ∀ j<N, ∀ i : Fin 7,
      (st (j+1)).coefficient 0 i=(evaluateFixedTaylorOrder S 60 h (st j))[i.val])
    (hmargin : ∀ j<N, checkBallCanonicalMargin
      (fun i=>((st j).coefficient 0 i).toRational S)=true)
    {p : Fin 3 → ℝ} (ha : ∀ i, ((st 0).coefficient 0 i).Contains S (shootingInitial p i))
    (hp : p 2=(N:ℝ)*(h:ℝ)) {U : ℝ} (hU : 0≤U) (horizon : (N:ℝ)*(h:ℝ)≤U) :
    ∀ i, (order60EndpointBalls S N st i).Contains
      (shootingFlow U hU (p 2) (shootingInitial p) i) := by
  have hT : 0≤(N:ℝ)*(h:ℝ) := mul_nonneg (Nat.cast_nonneg N) (Rat.cast_nonneg.mpr hh)
  have he := (checked_order60_shootingFlow hS hN hNmax hh hhmax st hcheck hglue hmargin ha).2 N le_rfl
  have hcompat := shootingFlow_horizon_compatibility hT hU horizon (shootingInitial p)
    (right_mem_Icc.mpr hT)
  intro i
  rw [hp,hcompat]
  exact he i

/-- Finite endpoint-ball radius checks discharge a root checker's actual
unweighted shooting-value error hypothesis. -/
theorem checked_order60_probe_output_error {S N : ℕ} (hS : 0<S) (hN : 0<N) (hNmax : N≤750)
    {h : ℚ} (hh : 0≤h) (hhmax : h≤1/100)
    (st : ℕ → FixedTaylorState)
    (hcheck : ∀ j<N, checkOrderTaylorData S 60 (st j)=true)
    (hglue : ∀ j<N, ∀ i : Fin 7,
      (st (j+1)).coefficient 0 i=(evaluateFixedTaylorOrder S 60 h (st j))[i.val])
    (hmargin : ∀ j<N, checkBallCanonicalMargin
      (fun i=>((st j).coefficient 0 i).toRational S)=true)
    {p : Fin 3 → ℝ} (ha : ∀ i, ((st 0).coefficient 0 i).Contains S (shootingInitial p i))
    (hp : p 2=(N:ℝ)*(h:ℝ)) {U : ℝ} (hU : 0≤U) (horizon : (N:ℝ)*(h:ℝ)≤U)
    {η : ℚ} (hη : 0≤η) (hrad : ∀ i, (projectBallVector (order60EndpointBalls S N st) i).radius≤η) :
    ‖projectedBallCenter (order60EndpointBalls S N st)-actualShootingMap U hU p‖≤(η:ℝ) := by
  exact projectedBallCenter_error hη
    (checked_order60_probe_endpoint hS hN hNmax hh hhmax st hcheck hglue hmargin ha hp hU horizon) hrad

/-- The raw-output error scale1e-40 still fits the intended finite-difference
and Newton budgets with the proved conservative derivative variation6e14. -/
theorem raw_output_newton_arithmetic_budget :
    (1/(10:ℝ)^9)+2*(3*((6*10^14)*(1/10^25)+(1/10^40)/(1/10^25))+
      (6*10^14)*(1/10^28))<2/10^9 := by norm_num

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.checked_order60_probe_output_error

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.MetricStability).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Actual shooting-probe bridge audit passed for {checked} declarations."
