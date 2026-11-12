import CentroidEscape.FivePathJacobian
import CentroidEscape.MatrixCertificate

/-!
# Computable rational data for the five-path shooting certificate

Rows/columns are aligned explicitly with the actual continuous linear
operator. Output radii and the center's seventh-coordinate moment margin
are finite rational checks.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

def projectedRationalCenter (b : BallVector) : RationalVector3 :=
  fun i=>(projectBallVector b i).center

lemma cast_projectedRationalCenter (b : BallVector) :
    castRationalVector3 (projectedRationalCenter b)=projectedBallCenter b := rfl

def fivePathRationalJacobian (δ : ℚ) (yp ym : Fin 2 → RationalVector3)
    (vt : RationalVector3) : RationalMatrix3 :=
  fun i=>![(yp 0 i-ym 0 i)/(2*δ),(yp 1 i-ym 1 i)/(2*δ),vt i]

/-- The checked matrix uses rows i and columns j in the same orientation
as the actual mixed finite-difference/time-field Jacobian. -/
theorem fivePathRationalJacobian_operator (δ : ℚ) (yp ym : Fin 2 → RationalVector3)
    (vt : RationalVector3) :
    rationalMatrixOperator (fivePathRationalJacobian δ yp ym vt)=
      fivePathJacobian (δ:ℝ) (fun i=>castRationalVector3 (yp i))
        (fun i=>castRationalVector3 (ym i)) (castRationalVector3 vt) := by
  ext v i
  simp [rationalMatrixOperator_apply,fivePathRationalJacobian,fivePathJacobian,
    columnOperator_apply,Finset.sum_apply,Fin.sum_univ_succ,castRationalVector3,
    Pi.smul_apply,smul_eq_mul]
  ring

def checkProjectedRadius (b : BallVector) (η : ℚ) : Bool :=
  decide (0≤η ∧ ∀ i : Fin 3, (projectBallVector b i).radius≤η)

theorem checkProjectedRadius_sound {b : BallVector} {η : ℚ}
    (hcheck : checkProjectedRadius b η=true) {z : WeightedState}
    (hb : ∀ i, (b i).Contains (z i)) :
    ‖castRationalVector3 (projectedRationalCenter b)-shootingProjection z‖≤(η:ℝ) := by
  have h : 0≤η ∧ ∀ i : Fin 3, (projectBallVector b i).radius≤η := of_decide_eq_true hcheck
  rw [cast_projectedRationalCenter]
  exact projectedBallCenter_error h.1 hb h.2

def checkMomentMargin (b : BallVector) (r : ℚ) : Bool :=
  decide (7000000*r<(b 6).center-(b 6).radius)

theorem checkMomentMargin_sound {b : BallVector} {r : ℚ}
    (hcheck : checkMomentMargin b r=true) {z : WeightedState}
    (hb : ∀ i, (b i).Contains (z i)) : (7000000:ℝ)*(r:ℝ)<z 6 := by
  have h : (7000000:ℚ)*r<(b 6).center-(b 6).radius := of_decide_eq_true hcheck
  have hr := (Rat.cast_lt (K:=ℝ)).mpr h
  norm_num only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_sub] at hr
  have hlow := (abs_le.mp (hb 6)).1
  linarith

/-- The finite check on the center endpoint's seventh coordinate supplies
the exact moment condition used by the geometric escape theorem. -/
theorem checked_center_moment_margin {T : ℝ} (hT : 0≤T)
    {p : Fin 3 → ℝ} (hcenter : p 2=T) {b : BallVector}
    (hb : ∀ i, (b i).Contains (shootingFlow (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT) (p 2) (shootingInitial p) i))
    {r : ℚ} (hcheck : checkMomentMargin b r=true) :
    (7000000:ℝ)*(r:ℝ)<shootingFlow T hT T (shootingInitial p) 6 := by
  have hm := checkMomentMargin_sound hcheck hb
  rw [hcenter,shootingFlow_horizon_compatibility hT (shootingExtendedHorizon_nonneg hT)
    (show T≤shootingExtendedHorizon T by unfold shootingExtendedHorizon; linarith)
    (shootingInitial p) (right_mem_Icc.mpr hT)] at hm
  exact hm

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.fivePathRationalJacobian_operator
#print axioms CentroidEscape.MetricStability.checked_center_moment_margin

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
  logInfo m!"Five-path rational-data audit passed for {checked} declarations."
