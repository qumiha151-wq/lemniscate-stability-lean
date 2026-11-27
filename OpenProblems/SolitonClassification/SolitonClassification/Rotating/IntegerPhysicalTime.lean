import SolitonClassification.Rotating.IntegerPhysicalCurvature

namespace SolitonClassification.Rotating.IntegerTarget.Physical
noncomputable section
open Set Real MeasureTheory NormalEvolution
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

variable (P : Seed)

def normalX (t s : ℝ) : ℝ := normalLogX P (logClock t) s
def normalY (t s : ℝ) : ℝ := normalLogY P (logClock t) s

theorem normalX_joint_smooth : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => normalX P z.1 z.2)
    (Ioi (-1/4) ×ˢ (univ : Set ℝ)) := by
  intro z hz
  have hc : ContDiffAt ℝ ∞ (fun w : ℝ×ℝ => logClock w.1) z :=
    (logClock_smoothAt hz.1).comp z contDiffAt_fst
  exact ((normalLogX_joint_smooth P).contDiffAt.comp z (hc.prodMk contDiffAt_snd)).contDiffWithinAt

theorem normalY_joint_smooth : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => normalY P z.1 z.2)
    (Ioi (-1/4) ×ˢ (univ : Set ℝ)) := by
  intro z hz
  have hc : ContDiffAt ℝ ∞ (fun w : ℝ×ℝ => logClock w.1) z :=
    (logClock_smoothAt hz.1).comp z contDiffAt_fst
  exact ((normalLogY_joint_smooth P).contDiffAt.comp z (hc.prodMk contDiffAt_snd)).contDiffWithinAt

theorem normalX_spatial_smooth (t : ℝ) : ContDiff ℝ ∞ (normalX P t) :=
  (normalLogX_joint_smooth P).comp (contDiff_const.prodMk contDiff_id)
theorem normalY_spatial_smooth (t : ℝ) : ContDiff ℝ ∞ (normalY P t) :=
  (normalLogY_joint_smooth P).comp (contDiff_const.prodMk contDiff_id)

theorem normalX_initial (s : ℝ) : normalX P 0 s=P.I.x s := by
  rw [normalX,logClock_zero,normalLogX_initial]
theorem normalY_initial (s : ℝ) : normalY P 0 s=P.I.y s := by
  rw [normalY,logClock_zero,normalLogY_initial]

theorem normalX_periodic (t : ℝ) : Function.Periodic (normalX P t) P.L :=
  normalLogX_periodic P (logClock t)
theorem normalY_periodic (t : ℝ) : Function.Periodic (normalY P t) P.L :=
  normalLogY_periodic P (logClock t)

theorem normal_metric (t s : ℝ) :
    deriv (normalX P t) s^2+deriv (normalY P t) s^2=
      (dilationScale t*scalarJacobian (physicalField P) (logClock t) s)^2 :=
  normalLog_metric P (logClock t) s

theorem normal_immersion (t s : ℝ) :
    0<deriv (normalX P t) s^2+deriv (normalY P t) s^2 :=
  normalLog_immersion P (logClock t) s

theorem normalX_time_derivative {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    HasDerivAt (fun u => normalX P u s)
      (exp (-3*logClock t)*profileForce P (normalParameter P (logClock t) s)*
        rotatedTangentY P (logClock t) (normalParameter P (logClock t) s)) t := by
  convert! (normalLogX_time_derivative P (logClock t) s).scomp t
    (logClock_hasDerivAt ht) using 1
  rw [←clock_scale_velocity (logClock t)]
  simp only [smul_eq_mul]
  ring

theorem normalY_time_derivative {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    HasDerivAt (fun u => normalY P u s)
      (-exp (-3*logClock t)*profileForce P (normalParameter P (logClock t) s)*
        rotatedTangentX P (logClock t) (normalParameter P (logClock t) s)) t := by
  convert! (normalLogY_time_derivative P (logClock t) s).scomp t
    (logClock_hasDerivAt ht) using 1
  rw [←clock_scale_velocity (logClock t)]
  simp only [smul_eq_mul]
  ring

theorem normal_velocity_tangent_zero {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    deriv (fun u => normalX P u s) t*deriv (normalX P t) s+
      deriv (fun u => normalY P u s) t*deriv (normalY P t) s=0 := by
  rw [(normalX_time_derivative P ht s).deriv,(normalY_time_derivative P ht s).deriv]
  change _*deriv (normalLogX P (logClock t)) s+
    _*deriv (normalLogY P (logClock t)) s=0
  rw [(normalLogX_spatial_derivative P _ _).deriv,(normalLogY_spatial_derivative P _ _).deriv]
  ring

end
end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.normalX_time_derivative
