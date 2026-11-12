import SolitonClassification.Rotating.RotatingNormalEvolutionLog
import SolitonClassification.Rotating.RotatingNormalEvolutionClock

/-! Actual physical-time rotating/dilating evolution, with the global scalar
reparameterization already constructed. The open domain contains all t>=0. -/
namespace SolitonClassification.Rotating.NormalEvolution
noncomputable section
open Set Real
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

variable (a : State) (L : ℝ) (h : IsClosedRotatingProfile a L)

def normalX (t s : ℝ) : ℝ := normalLogX a L h (logClock t) s
def normalY (t s : ℝ) : ℝ := normalLogY a L h (logClock t) s

theorem normalX_joint_smooth : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => normalX a L h z.1 z.2)
    (Ioi (-1/4) ×ˢ (univ : Set ℝ)) := by
  intro z hz
  have hc : ContDiffAt ℝ ∞ (fun w : ℝ×ℝ => logClock w.1) z :=
    (logClock_smoothAt hz.1).comp z contDiffAt_fst
  exact ((normalLogX_joint_smooth a L h).contDiffAt.comp z (hc.prodMk contDiffAt_snd)).contDiffWithinAt

theorem normalY_joint_smooth : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => normalY a L h z.1 z.2)
    (Ioi (-1/4) ×ˢ (univ : Set ℝ)) := by
  intro z hz
  have hc : ContDiffAt ℝ ∞ (fun w : ℝ×ℝ => logClock w.1) z :=
    (logClock_smoothAt hz.1).comp z contDiffAt_fst
  exact ((normalLogY_joint_smooth a L h).contDiffAt.comp z (hc.prodMk contDiffAt_snd)).contDiffWithinAt

theorem normalX_spatial_smooth (t : ℝ) : ContDiff ℝ ∞ (normalX a L h t) :=
  (normalLogX_joint_smooth a L h).comp (contDiff_const.prodMk contDiff_id)
theorem normalY_spatial_smooth (t : ℝ) : ContDiff ℝ ∞ (normalY a L h t) :=
  (normalLogY_joint_smooth a L h).comp (contDiff_const.prodMk contDiff_id)

theorem normalX_initial (s : ℝ) : normalX a L h 0 s=rotatingX a s := by
  rw [normalX,logClock_zero,normalLogX_initial]
theorem normalY_initial (s : ℝ) : normalY a L h 0 s=rotatingY a s := by
  rw [normalY,logClock_zero,normalLogY_initial]

theorem normalX_periodic (t : ℝ) : Function.Periodic (normalX a L h t) L :=
  normalLogX_periodic a L h (logClock t)
theorem normalY_periodic (t : ℝ) : Function.Periodic (normalY a L h t) L :=
  normalLogY_periodic a L h (logClock t)

theorem normal_metric (t s : ℝ) :
    deriv (normalX a L h t) s^2+deriv (normalY a L h t) s^2=
      (dilationScale t*scalarJacobian (rotatingReparamField a L h) (logClock t) s)^2 :=
  normalLog_metric a L h (logClock t) s

theorem normal_immersion (t s : ℝ) :
    0<deriv (normalX a L h t) s^2+deriv (normalY a L h t) s^2 :=
  normalLog_immersion a L h (logClock t) s

theorem normalX_time_derivative {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    HasDerivAt (fun u => normalX a L h u s)
      (exp (-3*logClock t)*profileForce a (normalParameter a L h (logClock t) s)*
        rotatedTangentY a (logClock t) (normalParameter a L h (logClock t) s)) t := by
  convert! (normalLogX_time_derivative a L h (logClock t) s).scomp t
    (logClock_hasDerivAt ht) using 1
  rw [←clock_scale_velocity (logClock t)]
  simp only [smul_eq_mul]
  ring

theorem normalY_time_derivative {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    HasDerivAt (fun u => normalY a L h u s)
      (-exp (-3*logClock t)*profileForce a (normalParameter a L h (logClock t) s)*
        rotatedTangentX a (logClock t) (normalParameter a L h (logClock t) s)) t := by
  convert! (normalLogY_time_derivative a L h (logClock t) s).scomp t
    (logClock_hasDerivAt ht) using 1
  rw [←clock_scale_velocity (logClock t)]
  simp only [smul_eq_mul]
  ring

theorem normal_velocity_tangent_zero {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    deriv (fun u => normalX a L h u s) t*deriv (normalX a L h t) s+
      deriv (fun u => normalY a L h u s) t*deriv (normalY a L h t) s=0 := by
  rw [(normalX_time_derivative a L h ht s).deriv,(normalY_time_derivative a L h ht s).deriv]
  change _*deriv (normalLogX a L h (logClock t)) s+
    _*deriv (normalLogY a L h (logClock t)) s=0
  rw [(normalLogX_spatial_derivative a L h _ _).deriv,(normalLogY_spatial_derivative a L h _ _).deriv]
  ring

end
end SolitonClassification.Rotating.NormalEvolution

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Actual physical-time curve audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Actual physical-time closed curve audited: {count} declarations; standard axioms only."
