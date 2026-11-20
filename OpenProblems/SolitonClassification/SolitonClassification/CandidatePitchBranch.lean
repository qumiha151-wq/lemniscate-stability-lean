import SolitonClassification.PitchContinuation
import SolitonClassification.Rotating.CandidateFinalAssembly

/-! The same five candidate enclosures used for the single rotating root
suffice for a branch with a dense set of actual noncircular closed pitches.
The five enclosure premises remain explicit. -/
noncomputable section
namespace SolitonClassification.Rotating.CandidatePitchBranch
open Set Metric CandidateRootBudget
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def angleDirection : Parameters := ![0,0,0,0,1]
def targetRadius : ℝ := radius/200

private theorem direction_norm : ‖angleDirection‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro i
  fin_cases i <;> norm_num [angleDirection]

private theorem preconditioned_direction : ‖CandidatePreconditioner.B angleDirection‖ ≤ 82 := by
  have hh := CandidatePreconditioner.B.le_opNorm angleDirection
  have h := mul_le_mul CandidatePreconditioner.actual_preconditioner_norm direction_norm
    (norm_nonneg _) (by norm_num)
  exact hh.trans (by simpa using h)

private theorem rotation_column : CandidatePreconditioner.B angleDirection 4 < -10 := by
  have hc : CandidatePreconditioner.rawB 4 4 < -10 := by decide +kernel
  have hr : ((CandidatePreconditioner.rawB 4 4:ℚ):ℝ)< -10 := by exact_mod_cast hc
  simpa [CandidatePreconditioner.B,parameterMatrixOperator_apply,angleDirection,
    Fin.sum_univ_succ] using hr

theorem shifted_endpoint_match (e : Fin 2 → ℝ) (c : Parameters) (t : ℝ)
    (h : actualShootingMap e c = t • angleDirection) :
    rotatingTrajectory (shootingInitial e c) (c 2) =
      rotatingTrajectory (shootingInitial e c) (-c 2) + angleVector (-112*Real.pi/57+t) := by
  let x := rotatingTrajectory (shootingInitial e c) (c 2)
  let y := rotatingTrajectory (shootingInitial e c) (-c 2)
  change shootingProjection (x-y)+shootingTarget=t • angleDirection at h
  rw [shootingProjection_apply] at h
  change x=y+angleVector (-112*Real.pi/57+t)
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  simp [shootingTarget,angleDirection] at h0 h1 h2 h3 h4
  ext i
  fin_cases i
  · simpa [angleVector] using sub_eq_zero.mp h0
  · simpa [angleVector] using sub_eq_zero.mp h1
  · simpa [angleVector] using sub_eq_zero.mp h2
  · simpa [angleVector] using sub_eq_zero.mp h3
  · simp [angleVector,x,y,rotatingTrajectory_parameter_constant]
  · change x 5=y 5+(-112*Real.pi/57+t)
    linarith

/-- The certificate hypotheses are exactly the five analytic/numerical
enclosures of CandidateFinalAssembly. Every realized member in the density
conclusion is an actual positive-pitch nonconstant closed planar expander. -/
theorem actual_closed_pitch_dense_of_remaining_enclosures
    (plus : ActualFlowMatrixBounds 1 (by norm_num) horizon Candidate.initial tubeRadius initialSet 8000 16000)
    (minus : ActualFlowMatrixBounds (-1) (by norm_num) horizon Candidate.initial tubeRadius initialSet 8000 16000)
    (y : Parameters)
    (hvalue : ‖y-actualShootingMap CandidateInputs.phaseReal candidateParameterCenter‖≤(1:ℝ)/10^27)
    (hjacobian : ‖CandidatePreconditioner.J-
      actualShootingDerivative CandidateInputs.phaseReal candidateParameterCenter‖≤(1:ℝ)/10^5)
    (hresidual : ‖CandidatePreconditioner.B y‖≤(1:ℝ)/10^30) :
    ∃ lo hi : ℝ, 0<lo ∧ lo<hi ∧
      ∀ x y : ℝ, lo≤x → x<y → y≤hi →
        ∃ c : Parameters, ∃ u : ℚ, x<c 4 ∧ c 4<y ∧
          IsClosedRotatingProfile (shootingInitial CandidateInputs.phaseReal c) ((u.den:ℝ)*(2*c 2)) ∧
          ¬∃ k : ℝ, ∀ s, rotatingK (shootingInitial CandidateInputs.phaseReal c) s=k := by
  let e := CandidateInputs.phaseReal
  let F := actualShootingMap e
  let D := actualShootingDerivative e
  let B := CandidatePreconditioner.B
  let p := candidateParameterCenter
  have hR : 0<tubeRadius := by have h:=radius_pos; dsimp [tubeRadius]; positivity
  have hsub : initialSet ⊆ ball Candidate.initial tubeRadius := by
    intro a ha
    have h := mem_ball.mp (initial_set_inside_quarter_tube ha)
    exact mem_ball.mpr (by linarith)
  let P := plus.toTrueCertificate hsub
  let M := minus.toTrueCertificate hsub
  have hdF (z) (hz : z∈closedBall p radius) : HasFDerivAt F (D z) z := by
    obtain ⟨ht,hs⟩ := parameter_domain hz
    exact (actualShootingMap_hasStrictFDerivAt e horizon hR plus.tube minus.tube
      ht (initial_set_inside_quarter_tube hs)).hasFDerivAt
  have hD (z) (hz : z∈closedBall p radius) :
      ‖ContinuousLinearMap.id ℝ Parameters - B.comp (D z)‖ ≤ (contraction:ℝ) := by
    have var := actualShootingDerivative_sharp_variation e CandidateInputs.phase_bounds.1
      CandidateInputs.phase_bounds.2 horizon_bounds.1.le hR (by norm_num) (by norm_num)
      plus.tube minus.tube (convex_closedBall Candidate.initial radius) initial_set_inside_quarter_tube
      P.derivativeBound M.derivativeBound P.inverse M.inverse P.inverseContinuous M.inverseContinuous
      P.inverseIdentity M.inverseIdentity P.inverseBound M.inverseBound
      (parameter_domain hz) (parameter_domain (mem_closedBall_self radius_pos.le))
    exact (preconditioned_derivative_from_center D B CandidatePreconditioner.J (by norm_num)
      (by have h := horizon_bounds.1; dsimp [trueJointVariationBudget]; positivity)
      CandidatePreconditioner.actual_preconditioner_norm
      hjacobian var (mem_closedBall.mp hz) CandidatePreconditioner.actual_preconditioner_defect).trans
      contraction_budget
  let η : ℝ := (1:ℝ)/10^30+82*(1/10^27)
  have center : ‖B (F p)‖ ≤ η := by
    have differ := B.le_opNorm (y-F p)
    rw [map_sub, norm_sub_rev] at differ
    have h := mul_le_mul CandidatePreconditioner.actual_preconditioner_norm hvalue
      (norm_nonneg _) (by norm_num)
    have tri := norm_sub_le_norm_sub_add_norm_sub (B (F p)) (B y) 0
    simp only [sub_zero] at tri
    dsimp only [η]; linarith
  have hτ : 0<targetRadius := by dsimp [targetRadius]; exact div_pos radius_pos (by norm_num)
  have self : η+targetRadius*‖B angleDirection‖+(contraction:ℝ)*radius≤radius := by
    have b := mul_le_mul_of_nonneg_left preconditioned_direction hτ.le
    calc
      _ ≤ η+targetRadius*82+(contraction:ℝ)*radius := by linarith
      _ ≤ _ := by norm_num [η,targetRadius,radius,contraction,candidateWideTimeRadius]
  have neg : B angleDirection 4+(contraction:ℝ)*‖B angleDirection‖/(1-(contraction:ℝ))<0 := by
    have b := preconditioned_direction
    have bb := rotation_column
    dsimp only [B,contraction]
    norm_num
    linarith only [b,bb]
  obtain ⟨c,hc,_,anti,dense⟩ := PitchContinuation.dense_pitch_of_certificate
    (θ := -112*Real.pi/57) (4:Fin 5) F D B p angleDirection contraction radius_pos.le
    hτ (by norm_num [contraction]) CandidatePreconditioner.actual_preconditioner_injective
    hdF hD center self neg
  have hl : -targetRadius<targetRadius := by linarith
  have ha := left_mem_Icc.mpr hl.le
  have hb := right_mem_Icc.mpr hl.le
  refine ⟨c targetRadius 4,c (-targetRadius) 4,
    (CandidateInputs.parameter_signs_of_ball (r:=radius) le_rfl (hc _ hb).1).2.1,
    anti ha hb hl,?_⟩
  intro x y hx hxy hy
  obtain ⟨t,ht,hx',hy',u,hu⟩ := dense x y hx hxy hy
  obtain ⟨hmem,hs⟩ := hc _ ht
  have hmatch := shifted_endpoint_match e (c t) t hs
  have signs := CandidateInputs.parameter_signs_of_ball (r:=radius) le_rfl hmem
  have tube := CandidateFinalAssembly.two_sided_tube_of_parameter_ball plus.tube minus.tube hmem
  have hol : (u.den:ℝ)*(-112*Real.pi/57+t)=(u.num:ℝ)*(2*Real.pi) := by
    rw [hu,Rat.cast_def]
    have hd : (u.den:ℝ)≠0 := by exact_mod_cast u.den_nz
    field_simp [hd]
  exact ⟨c t,u,hx',hy',closed_rotating_profile_of_endpoint signs.2.2 hmatch tube u.den
    u.den_pos u.num hol, rotatingK_nonconstant_of_initial_bound signs.2.2 hmatch tube
    (by simpa [shootingInitial_apply] using signs.1)⟩

end SolitonClassification.Rotating.CandidatePitchBranch

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf n || (`ClosedSimilarity).isPrefixOf n then
      for ax in (← collectAxioms n) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains ax do
          throwError "Candidate pitch branch audit failed for {n} at {ax}"
      count := count+1
  logInfo m!"Candidate actual pitch branch audited for {count} declarations."
