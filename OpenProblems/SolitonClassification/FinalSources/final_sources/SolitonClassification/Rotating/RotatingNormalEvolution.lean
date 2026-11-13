module

public import SolitonClassification.Rotating.RotatingNormalEvolutionTime
public import SolitonClassification.Rotating.RotatingNormalEvolutionCurvature
public import SolitonClassification.Rotating.RotatingClosedProfileShooting

@[expose] public section

/-! A genuine pure-normal free elastic evolution of the actual closed
rotating profile. Speed, curvature, elastic force and unit normal are all
computed from coordinate derivatives. A concrete shooting zero remains an
explicit input in the final shooting corollary; no numerical root is asserted. -/
namespace SolitonClassification.Rotating.NormalEvolution
noncomputable section
open Set Real MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- Actual geometric PDE on the open time interval containing every t>=0.
The equation is for the full time derivative, with no tangential term. -/
structure IsPureNormalElasticEvolution (L : ℝ) (X Y : ℝ → ℝ → ℝ) : Prop where
  period_pos : 0<L
  smooth_X : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => X z.1 z.2) (Ioi (-1/4) ×ˢ univ)
  smooth_Y : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => Y z.1 z.2) (Ioi (-1/4) ×ˢ univ)
  closed_X : ∀t, -1/4<t → Function.Periodic (X t) L
  closed_Y : ∀t, -1/4<t → Function.Periodic (Y t) L
  regular : ∀t, -1/4<t → ∀s, 0<curveSpeed (X t) (Y t) s
  evolution_X : ∀t, -1/4<t → ∀s, HasDerivAt (fun u => X u s)
    (-intrinsicElasticForce (X t) (Y t) s*unitNormalX (X t) (Y t) s) t
  evolution_Y : ∀t, -1/4<t → ∀s, HasDerivAt (fun u => Y u s)
    (-intrinsicElasticForce (X t) (Y t) s*unitNormalY (X t) (Y t) s) t

variable (a : State) (L : ℝ) (h : IsClosedRotatingProfile a L)

theorem normal_speed_eq (t s : ℝ) : curveSpeed (normalX a L h t) (normalY a L h t) s=
    dilationScale t*scalarJacobian (rotatingReparamField a L h) (logClock t) s :=
  normalLog_speed_eq a L h (logClock t) s

theorem normal_speed_pos (t s : ℝ) : 0<curveSpeed (normalX a L h t) (normalY a L h t) s :=
  normalLog_speed_pos a L h (logClock t) s

theorem normal_curvature (t s : ℝ) : intrinsicCurvature (normalX a L h t) (normalY a L h t) s=
    exp (-logClock t)*rotatingK a (normalParameter a L h (logClock t) s) :=
  normalLog_curvature a L h (logClock t) s

theorem normal_force (t s : ℝ) : intrinsicElasticForce (normalX a L h t) (normalY a L h t) s=
    exp (-3*logClock t)*profileForce a (normalParameter a L h (logClock t) s) :=
  normalLog_force a L h (logClock t) s

theorem normal_unitNormalX (t s : ℝ) : unitNormalX (normalX a L h t) (normalY a L h t) s=
    -rotatedTangentY a (logClock t) (normalParameter a L h (logClock t) s) :=
  normalLog_normalX a L h (logClock t) s

theorem normal_unitNormalY (t s : ℝ) : unitNormalY (normalX a L h t) (normalY a L h t) s=
    rotatedTangentX a (logClock t) (normalParameter a L h (logClock t) s) :=
  normalLog_normalY a L h (logClock t) s

theorem normalX_free_elastic {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    HasDerivAt (fun u => normalX a L h u s)
      (-intrinsicElasticForce (normalX a L h t) (normalY a L h t) s*
        unitNormalX (normalX a L h t) (normalY a L h t) s) t := by
  convert! normalX_time_derivative a L h ht s using 1
  rw [normal_force,normal_unitNormalX]
  ring

theorem normalY_free_elastic {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    HasDerivAt (fun u => normalY a L h u s)
      (-intrinsicElasticForce (normalX a L h t) (normalY a L h t) s*
        unitNormalY (normalX a L h t) (normalY a L h t) s) t := by
  convert! normalY_time_derivative a L h ht s using 1
  rw [normal_force,normal_unitNormalY]
  ring

theorem normalEvolution_is_pure_normal :
    IsPureNormalElasticEvolution L (normalX a L h) (normalY a L h) where
  period_pos := h.1
  smooth_X := normalX_joint_smooth a L h
  smooth_Y := normalY_joint_smooth a L h
  closed_X := fun t _ => normalX_periodic a L h t
  closed_Y := fun t _ => normalY_periodic a L h t
  regular := fun t _ => normal_speed_pos a L h t
  evolution_X := fun _ ht => normalX_free_elastic a L h ht
  evolution_Y := fun _ ht => normalY_free_elastic a L h ht

theorem scalarFlow_jacobian_integral (g : PeriodicScalarField) (τ : ℝ) :
    (∫s in 0..g.period, scalarJacobian g τ s)=g.period := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => scalarFlow_hasDerivAt_initial g τ s)
    ((scalarJacobian_spatial_smooth g τ).continuous.intervalIntegrable _ _)]
  have hp := scalarFlow_period_add g τ 0
  simp only [zero_add] at hp
  rw [hp]
  ring

theorem normal_length (t : ℝ) :
    (∫s in 0..L,curveSpeed (normalX a L h t) (normalY a L h t) s)=dilationScale t*L := by
  simp_rw [normal_speed_eq]
  rw [intervalIntegral.integral_const_mul]
  have hi := scalarFlow_jacobian_integral (rotatingReparamField a L h) (logClock t)
  change (∫s in 0..L,scalarJacobian (rotatingReparamField a L h) (logClock t) s)=L at hi
  rw [hi]

theorem normalEvolution_future (t : ℝ) (ht : 0≤t) (s : ℝ) :
    HasDerivAt (fun u => normalX a L h u s)
      (-intrinsicElasticForce (normalX a L h t) (normalY a L h t) s*
        unitNormalX (normalX a L h t) (normalY a L h t) s) t ∧
    HasDerivAt (fun u => normalY a L h u s)
      (-intrinsicElasticForce (normalX a L h t) (normalY a L h t) s*
        unitNormalY (normalX a L h t) (normalY a L h t) s) t :=
  ⟨normalX_free_elastic a L h (by linarith) s,normalY_free_elastic a L h (by linarith) s⟩

/-- The genuine shooting root and finite support-tube certificate are still
inputs. The output is a full pure-normal PDE, not only normal-component motion. -/
theorem actualShooting_exists_pure_normal_evolution (e : Fin 2 → ℝ) (c : Parameters)
    (hT : 0<c 2) (hzero : actualShootingMap e c=0)
    (htube : ∀s∈Icc (-c 2) (c 2),rotatingTrajectory (shootingInitial e c) s∈outerTube) :
    ∃ X Y : ℝ → ℝ → ℝ, IsPureNormalElasticEvolution (114*c 2) X Y ∧
      (∀s,X 0 s=rotatingX (shootingInitial e c) s ∧ Y 0 s=rotatingY (shootingInitial e c) s) ∧
      (∀t,(∫s in 0..(114*c 2),curveSpeed (X t) (Y t) s)=dilationScale t*(114*c 2)) := by
  let hp := actualShooting_closed_profile e c hT hzero htube
  refine ⟨normalX _ _ hp,normalY _ _ hp,normalEvolution_is_pure_normal _ _ hp,?_,normal_length _ _ hp⟩
  exact fun s => ⟨normalX_initial _ _ hp s,normalY_initial _ _ hp s⟩

end
end SolitonClassification.Rotating.NormalEvolution

#print axioms SolitonClassification.Rotating.NormalEvolution.normalEvolution_is_pure_normal
#print axioms SolitonClassification.Rotating.NormalEvolution.actualShooting_exists_pure_normal_evolution
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Actual pure-normal elastic evolution audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Actual pure-normal free elastic evolution audited: {count} declarations; standard axioms only."
