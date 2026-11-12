import SolitonClassification.Rotating.ActualShooting
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.MeanValue

/-! Exact endpoint matching propagates by uniqueness of the actual
global clipped flow. The angle is not clipped and does not enter the
field, so an angle shift is an exact symmetry, not a periodicity premise. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

def angleVector (d : ℝ) : State := fun i => if i=5 then d else 0
def rotatingTrajectory (a : State) (t : ℝ) : State := supportFlow 1 (by norm_num) t a

theorem field_angle_invariant (x : State) (d : ℝ) : field (x+angleVector d)=field x := by
  ext i
  fin_cases i <;> simp [field,angleVector]

theorem clippedField_angle_invariant (x : State) (d : ℝ) :
    clippedField (x+angleVector d)=clippedField x := by
  have hc : clipState (x+angleVector d)=clipState x+angleVector d := by
    ext i
    fin_cases i <;> simp [clipState,angleVector]
  rw [clippedField,hc,field_angle_invariant]
  rfl

theorem rotatingTrajectory_zero (a : State) : rotatingTrajectory a 0=a := supportFlow_zero _ _ _

theorem rotatingTrajectory_derivative (a : State) (t : ℝ) :
    HasDerivAt (rotatingTrajectory a) (clippedField (rotatingTrajectory a t)) t := by
  convert! supportFlow_derivative 1 (by norm_num) a t using 1
  simp only [signedClippedField,one_smul,rotatingTrajectory]

theorem rotatingTrajectory_shift_derivative (a : State) (u t : ℝ) :
    HasDerivAt (fun s => rotatingTrajectory a (s+u)) (clippedField (rotatingTrajectory a (t+u))) t := by
  convert! (rotatingTrajectory_derivative a (t+u)).scomp t ((hasDerivAt_id t).add_const u) using 1
  simp only [one_smul]

theorem rotatingTrajectory_parameter_constant (a : State) (t : ℝ) : rotatingTrajectory a t 4=a 4 := by
  have hd (s : ℝ) : HasDerivAt (fun r => rotatingTrajectory a r 4) 0 s := by
    have h := (ContinuousLinearMap.proj (4:Fin 6) : State →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s
      (rotatingTrajectory_derivative a s)
    convert! h using 1
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa only [rotatingTrajectory_zero] using he

theorem rotatingTrajectory_shift_match {a : State} {u v d : ℝ}
    (hmatch : rotatingTrajectory a u=rotatingTrajectory a v+angleVector d) :
    ∀s,rotatingTrajectory a (s+u)=rotatingTrajectory a (s+v)+angleVector d := by
  have hf : (fun s => rotatingTrajectory a (s+u))=
      fun s => supportFlow 1 (by norm_num) s (rotatingTrajectory a u) := by
    apply supportFlow_unique 1 (by norm_num)
    · simp only [zero_add]
    · intro s
      simpa only [signedClippedField,one_smul] using rotatingTrajectory_shift_derivative a u s
  have hg : (fun s => rotatingTrajectory a (s+v)+angleVector d)=
      fun s => supportFlow 1 (by norm_num) s (rotatingTrajectory a u) := by
    apply supportFlow_unique 1 (by norm_num)
    · simpa only [zero_add] using hmatch.symm
    · intro s
      simpa only [signedClippedField,one_smul,clippedField_angle_invariant] using
        (rotatingTrajectory_shift_derivative a v s).add_const (angleVector d)
  exact fun s => congrFun (hf.trans hg.symm) s

theorem rotatingTrajectory_quasiperiodic {a : State} {T d : ℝ}
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d) :
    ∀s,rotatingTrajectory a (s+2*T)=rotatingTrajectory a s+angleVector d := by
  intro s
  have h := rotatingTrajectory_shift_match hmatch (s+T)
  simpa only [show s+T+T=s+2*T by ring,show s+T+(-T)=s by ring] using h

theorem rotatingTrajectory_coordinate_periodic {a : State} {T d : ℝ}
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d)
    (i : Fin 6) (hi : i≠5) : Function.Periodic (fun s => rotatingTrajectory a s i) (2*T) := by
  intro s
  have h := congrFun (rotatingTrajectory_quasiperiodic hmatch s) i
  simpa only [Pi.add_apply,angleVector,if_neg hi,add_zero] using h

theorem rotatingTrajectory_angle_shift {a : State} {T d : ℝ}
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d) :
    ∀s,rotatingTrajectory a (s+2*T) 5=rotatingTrajectory a s 5+d := by
  intro s
  simpa [angleVector] using
    congrFun (rotatingTrajectory_quasiperiodic hmatch s) (5:Fin 6)

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating exact endpoint-periodicity audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating exact endpoint-periodicity audit passed for {count} declarations."
