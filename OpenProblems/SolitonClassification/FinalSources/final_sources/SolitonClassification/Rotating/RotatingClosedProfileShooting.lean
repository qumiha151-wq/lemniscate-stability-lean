module

public import SolitonClassification.Rotating.RotatingClosedProfileClosure

@[expose] public section

/-! The actual five-dimensional shooting zero supplies exact endpoint
matching and angle increment -112*pi/57. The conserved b-coordinate is
proved from the actual ODE, completing the six-dimensional match. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem actualShooting_endpoint_match (e : Fin 2 → ℝ) (c : Parameters)
    (hzero : actualShootingMap e c=0) :
    rotatingTrajectory (shootingInitial e c) (c 2)=
      rotatingTrajectory (shootingInitial e c) (-c 2)+angleVector (-112*Real.pi/57) := by
  have h := (shootingMap_eq_zero_iff e actualFlow c).mp hzero
  change rotatingTrajectory (shootingInitial e c) (c 2) 0=rotatingTrajectory (shootingInitial e c) (-c 2) 0 ∧
    rotatingTrajectory (shootingInitial e c) (c 2) 1=rotatingTrajectory (shootingInitial e c) (-c 2) 1 ∧
    rotatingTrajectory (shootingInitial e c) (c 2) 2=rotatingTrajectory (shootingInitial e c) (-c 2) 2 ∧
    rotatingTrajectory (shootingInitial e c) (c 2) 3=rotatingTrajectory (shootingInitial e c) (-c 2) 3 ∧
    rotatingTrajectory (shootingInitial e c) (c 2) 5-rotatingTrajectory (shootingInitial e c) (-c 2) 5=
      -112*Real.pi/57 at h
  obtain ⟨h0,h1,h2,h3,h5⟩ := h
  ext i
  fin_cases i
  · simpa [angleVector] using h0
  · simpa [angleVector] using h1
  · simpa [angleVector] using h2
  · simpa [angleVector] using h3
  · simp [angleVector,rotatingTrajectory_parameter_constant]
  · change rotatingTrajectory (shootingInitial e c) (c 2) 5=
      rotatingTrajectory (shootingInitial e c) (-c 2) 5+(-112*Real.pi/57)
    linarith

theorem rotatingTrajectory_two_sided_tube {a : State} {T : ℝ}
    (hplus : ∀t∈Icc 0 T,supportFlow 1 (by norm_num) t a∈outerTube)
    (hminus : ∀t∈Icc 0 T,supportFlow (-1) (by norm_num) t a∈outerTube) :
    ∀t∈Icc (-T) T,rotatingTrajectory a t∈outerTube := by
  intro t ht
  by_cases hpos : 0≤t
  · exact hplus t ⟨hpos,ht.2⟩
  · have he : rotatingTrajectory a t=supportFlow (-1) (by norm_num) (-t) a :=
      actualFlow_reflected (t,a)
    rw [he]
    exact hminus (-t) ⟨by linarith,by linarith [ht.1]⟩

theorem actualShooting_global_original_smooth (e : Fin 2 → ℝ) (c : Parameters)
    (hT : 0<c 2) (hzero : actualShootingMap e c=0)
    (htube : ∀s∈Icc (-c 2) (c 2),rotatingTrajectory (shootingInitial e c) s∈outerTube) :
    ContDiff ℝ ∞ (rotatingTrajectory (shootingInitial e c)) ∧
      (∀s,HasDerivAt (rotatingTrajectory (shootingInitial e c))
        (field (rotatingTrajectory (shootingInitial e c) s)) s) := by
  have hg := rotatingTrajectory_global_tube hT (actualShooting_endpoint_match e c hzero) htube
  exact ⟨rotatingTrajectory_smooth_of_global_tube hg,rotatingTrajectory_original_derivative hg⟩

/-- A concrete property of the actual position, conditional only on a
true shooting zero, positive half-length, and finite-interval tube data.
After 57 support periods its angle changes by -56 full turns. -/
theorem actualShooting_closed_profile (e : Fin 2 → ℝ) (c : Parameters)
    (hT : 0<c 2) (hzero : actualShootingMap e c=0)
    (htube : ∀s∈Icc (-c 2) (c 2),rotatingTrajectory (shootingInitial e c) s∈outerTube) :
    IsClosedRotatingProfile (shootingInitial e c) (114*c 2) := by
  have hh := closed_rotating_profile_of_endpoint hT (actualShooting_endpoint_match e c hzero)
    htube 57 (by norm_num) (-56) (by norm_num; ring)
  have hlen : ((57:ℕ):ℝ)*(2*c 2)=114*c 2 := by ring
  rw [hlen] at hh
  exact hh

theorem actualShooting_total_curvature (e : Fin 2 → ℝ) (c : Parameters)
    (hT : 0<c 2) (hzero : actualShootingMap e c=0)
    (htube : ∀s∈Icc (-c 2) (c 2),rotatingTrajectory (shootingInitial e c) s∈outerTube) :
    (∫ s in 0..(114*c 2),rotatingK (shootingInitial e c) s)=(-56:ℝ)*(2*Real.pi) := by
  have hh := rotating_total_curvature hT (actualShooting_endpoint_match e c hzero)
    htube 57 (-56) (by norm_num; ring)
  have hlen : ((57:ℕ):ℝ)*(2*c 2)=114*c 2 := by ring
  rw [hlen] at hh
  simpa only [Int.cast_neg,Int.cast_ofNat] using hh

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual-shooting closed-geometry audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual-shooting closed-geometry audit passed for {count} declarations."
