import SolitonClassification.Rotating.FixedField

/-! Exact data from the reviewed rotating candidate. These declarations prove
initial/first-polynomial facts only. No ODE tail or periodic root is asserted. -/
namespace SolitonClassification.Rotating.Candidate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def parameters : Fin 5 → ℚ := ![(37504779682444386295590102548171085504930316329056138905412480845931391199264202271552753 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,(154422633850415199282735664653811140313613816683382659468655489386293680725237156019377301 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,(156080360716790281849844889560549805394762194677867378746575322740205093349685521380557013 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,(33524071104453057019595251486620171846814564624845582140267508740075917594413254066837557047857271368975681511888219706760368933478376532309744737384639852233464166614971095521867 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,(484330922742141770216725846681026856431953685029982528346012393610054374260218271253989139 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def phase : Fin 2 → ℚ := ![(-2997696555817197 : ℚ) / 50000000000000000,(-9982011451324311 : ℚ) / 10000000000000000]
def mesh : ℕ := 10^60
def rawInitial : Fin 6 → ℚ :=
  ![parameters 0,parameters 3*phase 0/8,parameters 1,parameters 3*phase 1,parameters 4,0]
noncomputable def initial : State := fun i => (rawInitial i : ℝ)
def initialBalls : BallState := fun i => FixedBall.ofRat mesh (rawInitial i)
def firstCoefficientBalls : BallState := fixedField mesh initialBalls
def step : ℚ := parameters 2/4000
def stepCap : ℚ := 1561/200000
def eulerBalls : BallState := fixedEuler mesh step initialBalls

theorem mesh_pos : 0<mesh := by norm_num [mesh]
theorem initial_enclosed (i : Fin 6) : (initialBalls i).Contains mesh (initial i) :=
  FixedBall.contains_ofRat mesh_pos _
theorem first_coefficient_enclosed (i : Fin 6) :
    (firstCoefficientBalls i).Contains mesh (field initial i) :=
  fixedField_contains mesh_pos initial_enclosed i
theorem first_polynomial_enclosed (i : Fin 6) :
    (eulerBalls i).Contains mesh ((initial+(step:ℝ) • field initial) i) :=
  fixedEuler_contains mesh_pos step initial_enclosed i

theorem half_length_bounds : (31:ℚ)<parameters 2 ∧ parameters 2<3122/100 := by
  decide +kernel
theorem positive_step : 0<step := by decide +kernel
theorem step_below_cap : step<stepCap := by decide +kernel
theorem cap_below_local_time : stepCap<1/125 := by norm_num [stepCap]

theorem state_tail_rational_budget :
    (10:ℚ)*(15*stepCap)^61/(1-15*stepCap)<2/10^56 := by norm_num [stepCap]
theorem matrix_tail_rational_budget :
    (15*stepCap)^61*((123:ℚ)/(1-15*stepCap)+2*(15*stepCap)/(1-15*stepCap)^2)
      <3/10^55 := by norm_num [stepCap]
theorem shooting_hessian_rational_budget :
    (16:ℚ)*(32*(4*2000)*(4*4000)*4*(4*2000)^2+2*17*(4*2000)+17*75)<10^20 := by
  norm_num

theorem first_coefficient_upper_checked :
    ((firstCoefficientBalls 1).toRational mesh).center+
      ((firstCoefficientBalls 1).toRational mesh).radius < (-26:ℚ) := by decide +kernel

theorem actual_initial_vprime_negative : 8*field initial 1 < -200 := by
  have h := (fixedBall_contains_lower_upper (first_coefficient_enclosed 1)).2
  have hc : (((firstCoefficientBalls 1).toRational mesh).center:ℝ)+
      ((firstCoefficientBalls 1).toRational mesh).radius < -26 := by
    exact_mod_cast first_coefficient_upper_checked
  linarith

end SolitonClassification.Rotating.Candidate

#print axioms SolitonClassification.Rotating.Candidate.actual_initial_vprime_negative
#print axioms SolitonClassification.Rotating.Candidate.first_polynomial_enclosed

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Rotating exact-seed/first-polynomial audit passed; no ODE/root claim."
