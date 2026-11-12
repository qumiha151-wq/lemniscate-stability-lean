"""Emit exact seed rationals and kernel-checked elementary certificate budgets.

The external file supplies data only. Every claimed inequality is proved
inside Lean with decide/norm_num; no native_decide or external proof oracle.
"""
from pathlib import Path
from fractions import Fraction
import json,hashlib
HERE=Path(__file__).resolve().parent
source=HERE.parent/'next_research'/'classification_odd_branch_interval'/'shooting_certificate.json'
record=json.loads(source.read_text())
def q(s):
    v=Fraction(s)
    return f'({v.numerator} : ℚ) / {v.denominator}'
params=','.join(q(x) for x in record['center_exact_decimal'])
phase=','.join(q(x) for x in record['phase_exact_decimal'])
text='''import SolitonClassification.Rotating.FixedField

/-! Exact data from the reviewed rotating candidate. These declarations prove
initial/first-polynomial facts only. No ODE tail or periodic root is asserted. -/
namespace SolitonClassification.Rotating.Candidate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def parameters : Fin 5 → ℚ := ![PARAMETERS]
def phase : Fin 2 → ℚ := ![PHASE]
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
'''.replace('PARAMETERS',params).replace('PHASE',phase)
target=HERE/'SolitonClassification'/'Rotating'/'CandidateInitial.lean'
target.write_text(text,encoding='utf-8')
(HERE/'candidate_input_provenance.json').write_text(json.dumps(dict(source=str(source),
  sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
  status='Untrusted exact rational data; emitted claims checked by Lean kernel'),indent=2)+'\n')
