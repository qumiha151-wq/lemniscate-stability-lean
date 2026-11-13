module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Lean.Util.CollectAxioms

@[expose] public section

/-! The actual physical/logarithmic time change, smooth on t>-1/4.
Its derivative is exactly the fourth-power inverse dilation factor. -/
namespace SolitonClassification.Rotating.NormalEvolution
noncomputable section
open Set Real
open scoped ContDiff
set_option Elab.async false

def logClock (t : ℝ) : ℝ := log (1+4*t)/4
def dilationScale (t : ℝ) : ℝ := exp (logClock t)

theorem logClock_zero : logClock 0=0 := by simp [logClock]
theorem dilationScale_pos (t : ℝ) : 0<dilationScale t := exp_pos _

theorem logClock_smoothAt {t : ℝ} (ht : -1/4<t) : ContDiffAt ℝ ∞ logClock t := by
  have hn : (1:ℝ)+4*t≠0 := ne_of_gt (by linarith)
  exact ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).log hn).div_const 4

theorem logClock_smooth : ContDiffOn ℝ ∞ logClock (Ioi (-1/4)) :=
  fun _ ht => (logClock_smoothAt ht).contDiffWithinAt

theorem exp_four_logClock {t : ℝ} (ht : -1/4<t) : exp (4*logClock t)=1+4*t := by
  rw [logClock,show 4*(log (1+4*t)/4)=log (1+4*t) by ring]
  exact exp_log (by linarith)

theorem dilationScale_pow_four {t : ℝ} (ht : -1/4<t) : dilationScale t^4=1+4*t := by
  rw [dilationScale,←exp_nat_mul]
  exact exp_four_logClock ht

theorem logClock_hasDerivAt {t : ℝ} (ht : -1/4<t) :
    HasDerivAt logClock (exp (-4*logClock t)) t := by
  have hn : (1:ℝ)+4*t≠0 := ne_of_gt (by linarith)
  have hd := (((hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).const_mul 4)).log hn).div_const 4
  convert! hd using 1
  rw [show -4*logClock t=-(4*logClock t) by ring,exp_neg,exp_four_logClock ht]
  simp only [Pi.add_apply,id_eq,zero_add,mul_one]
  field_simp [hn]

theorem clock_scale_velocity (τ : ℝ) : exp (-4*τ)*exp τ=exp (-3*τ) := by
  rw [←exp_add]
  congr 1
  ring

end
end SolitonClassification.Rotating.NormalEvolution

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Normal-evolution clock audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Actual normal-evolution clock audited: {count} declarations; standard axioms only."
