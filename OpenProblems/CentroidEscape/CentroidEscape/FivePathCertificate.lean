import CentroidEscape.FiniteShootingPath
import CentroidEscape.ShootingGeometryBridge

/-!
# One finite five-path certificate implies a smooth escaping FEF

The only hypothesis of the final theorem is a computable Boolean check on
finite rational/integer data. The theorem does not assume a true orbit,
shooting derivative, zero, or positive moment at an unknown root.
-/
namespace CentroidEscape.MetricStability
open Set Real Filter
open scoped Topology ContDiff NNReal
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

structure FivePathCertificateData where
  mesh : ℕ
  parameter : RationalVector3
  centerPath : FiniteShootingPath
  plusPath : Fin 2 → FiniteShootingPath
  minusPath : Fin 2 → FiniteShootingPath
  preconditioner : RationalMatrix3

namespace FivePathCertificateData

def step (d : FivePathCertificateData) : ℚ := d.parameter 2/750

def plusParameter (d : FivePathCertificateData) (i : Fin 2) : RationalVector3 :=
  d.parameter+(1/10^25:ℚ) • Pi.single (spatialParameterIndex i) 1

def minusParameter (d : FivePathCertificateData) (i : Fin 2) : RationalVector3 :=
  d.parameter-(1/10^25:ℚ) • Pi.single (spatialParameterIndex i) 1

def centerBall (d : FivePathCertificateData) : BallVector := d.centerPath.endpoint d.mesh
def fieldBall (d : FivePathCertificateData) : BallVector := evaluateWeightedField d.mesh d.centerBall
def centerOutput (d : FivePathCertificateData) : RationalVector3 := projectedRationalCenter d.centerBall
def plusOutput (d : FivePathCertificateData) (i : Fin 2) : RationalVector3 :=
  projectedRationalCenter ((d.plusPath i).endpoint d.mesh)
def minusOutput (d : FivePathCertificateData) (i : Fin 2) : RationalVector3 :=
  projectedRationalCenter ((d.minusPath i).endpoint d.mesh)
def jacobian (d : FivePathCertificateData) : RationalMatrix3 :=
  fivePathRationalJacobian (1/10^25) d.plusOutput d.minusOutput (projectedRationalCenter d.fieldBall)

def Valid (d : FivePathCertificateData) : Prop :=
  0<d.mesh ∧ 1≤d.parameter 2 ∧ d.parameter 2+1/16000≤15/2 ∧
  d.centerPath.check d.mesh d.step d.parameter=true ∧
  (∀ i : Fin 2, (d.plusPath i).check d.mesh d.step (d.plusParameter i)=true) ∧
  (∀ i : Fin 2, (d.minusPath i).check d.mesh d.step (d.minusParameter i)=true) ∧
  checkProjectedRadius d.fieldBall (1/10^40)=true ∧
  checkRationalMatrixBound d.preconditioner 2=true ∧
  checkRationalMatrixBound (rationalIdentity3-rationalMatrixProduct d.preconditioner d.jacobian) (1/10^9)=true ∧
  checkRationalVectorBound (rationalMatrixVector d.preconditioner d.centerOutput) (1/10^35)=true ∧
  checkMomentMargin d.centerBall (1/10^28)=true

instance (d : FivePathCertificateData) : Decidable d.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def check (d : FivePathCertificateData) : Bool := decide d.Valid

lemma plus_time (d : FivePathCertificateData) (i : Fin 2) : d.plusParameter i 2=d.parameter 2 := by
  fin_cases i <;> simp [plusParameter,spatialParameterIndex]

lemma minus_time (d : FivePathCertificateData) (i : Fin 2) : d.minusParameter i 2=d.parameter 2 := by
  fin_cases i <;> simp [minusParameter,spatialParameterIndex]

lemma cast_plusParameter (d : FivePathCertificateData) (i : Fin 2) :
    castRationalVector3 (d.plusParameter i)=castRationalVector3 d.parameter+
      (1/10^25:ℝ) • coordinateDirection (spatialParameterIndex i) := by
  ext j
  by_cases he : j=spatialParameterIndex i <;>
    simp [castRationalVector3,plusParameter,coordinateDirection,he]

lemma cast_minusParameter (d : FivePathCertificateData) (i : Fin 2) :
    castRationalVector3 (d.minusParameter i)=castRationalVector3 d.parameter-
      (1/10^25:ℝ) • coordinateDirection (spatialParameterIndex i) := by
  ext j
  by_cases he : j=spatialParameterIndex i <;>
    simp [castRationalVector3,minusParameter,coordinateDirection,he]

end FivePathCertificateData

noncomputable section

/-- Soundness of the complete finite certificate. Concrete data still have
to pass the stated check; this is not an assertion that they already do. -/
theorem checked_fivePathCertificate_yields_smooth_classical_FEF_escape
    (d : FivePathCertificateData) (hcheck : d.check=true) :
    ∃ L : ℝ, 0<L ∧ ∃ γ : ℝ → ℝ → Plane,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ=>γ q.1 q.2) {q | -1/4<q.1} ∧
      (∀t, Function.Periodic (γ t) (2*L) ∧ ContDiff ℝ ∞ (γ t)) ∧
      (∀t, 0≤t → ∀s, 0<‖deriv (γ t) s‖) ∧
      (∀t, 0≤t → ∀s, HasDerivAt (fun r=>γ r s)
        ((-curveElasticForce (γ t) s) • curveUnitNormal (γ t) s) t) ∧
      Tendsto (fun t=>curveCentroidX (2*L) (γ t)) atTop atTop := by
  have hv : d.Valid := of_decide_eq_true hcheck
  rcases hv with ⟨hS,hTminQ,hbudgetQ,hcc,hpc,hmc,htc,hBc,hJc,hyc,hmomc⟩
  let p₀ := castRationalVector3 d.parameter
  let T : ℝ := (d.parameter 2:ℝ)
  have hTmin : 1≤T := by
    change (1:ℝ)≤(d.parameter 2:ℝ)
    exact_mod_cast hTminQ
  have hT : 0<T := by linarith
  have hcenter : p₀ 2=T := rfl
  have hbudget : shootingExtendedHorizon T≤15/2 := by
    unfold shootingExtendedHorizon
    change (d.parameter 2:ℝ)+1/16000≤15/2
    have he := (Rat.cast_le (K:=ℝ)).mpr hbudgetQ
    norm_num only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at he
    exact he
  let U := shootingExtendedHorizon T
  let hU : 0≤U := shootingExtendedHorizon_nonneg hT.le
  have hh : 0≤d.step := by unfold FivePathCertificateData.step; linarith
  have hhmax : d.step≤1/100 := by unfold FivePathCertificateData.step; linarith
  have hTstep : T=(750:ℝ)*(d.step:ℝ) := by
    dsimp [T,FivePathCertificateData.step]
    push_cast
    ring
  have horizon : (750:ℝ)*(d.step:ℝ)≤U := by
    rw [← hTstep]
    dsimp [U,shootingExtendedHorizon]
    linarith
  have hc : ∀t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube := by
    have hinner := FiniteShootingPath.checked_inner hS hh hhmax hcc
    intro t ht
    have ht' : t∈Icc 0 ((750:ℝ)*(d.step:ℝ)) := by
      rw [← hTstep]
      exact ht
    have hcompat := shootingFlow_horizon_compatibility
      (mul_nonneg (by norm_num : (0:ℝ)≤750) (Rat.cast_nonneg.mpr hh)) hT.le
      (le_of_eq hTstep.symm) (shootingInitial p₀) ht'
    rw [hcompat]
    exact hinner t ht'
  have hb : ∀ i, (d.centerBall i).Contains (shootingFlow U hU (p₀ 2) (shootingInitial p₀) i) :=
    FiniteShootingPath.checked_endpoint hS hh hhmax hcc hTstep hU horizon
  have hy : ‖castRationalVector3 d.centerOutput-actualShootingMap U hU p₀‖≤(1/10^40:ℝ) :=
    FiniteShootingPath.checked_output hS hh hhmax hcc hTstep hU horizon
  have hp : ∀ i : Fin 2, ‖castRationalVector3 (d.plusOutput i)-
      actualShootingMap U hU (p₀+(1/10^25:ℝ) • coordinateDirection (spatialParameterIndex i))‖≤(1/10^40:ℝ) := by
    intro i
    have ht : (d.plusParameter i 2:ℝ)=(750:ℝ)*(d.step:ℝ) := by
      rw [FivePathCertificateData.plus_time]
      exact hTstep
    have he := FiniteShootingPath.checked_output hS hh hhmax (hpc i) ht hU horizon
    simpa only [FivePathCertificateData.cast_plusParameter,FivePathCertificateData.plusOutput,p₀] using he
  have hm : ∀ i : Fin 2, ‖castRationalVector3 (d.minusOutput i)-
      actualShootingMap U hU (p₀-(1/10^25:ℝ) • coordinateDirection (spatialParameterIndex i))‖≤(1/10^40:ℝ) := by
    intro i
    have ht : (d.minusParameter i 2:ℝ)=(750:ℝ)*(d.step:ℝ) := by
      rw [FivePathCertificateData.minus_time]
      exact hTstep
    have he := FiniteShootingPath.checked_output hS hh hhmax (hmc i) ht hU horizon
    simpa only [FivePathCertificateData.cast_minusParameter,FivePathCertificateData.minusOutput,p₀] using he
  have htvalid : 0≤(1/10^40:ℚ) ∧ ∀ i : Fin 3, (projectBallVector d.fieldBall i).radius≤1/10^40 :=
    of_decide_eq_true htc
  have hJreal := actual_fivePathJacobian_error hT hTmin hbudget hcenter hc
    (by norm_num : (0:ℝ)≤1/10^40) (by norm_num : (0:ℝ)<1/10^25)
    (by norm_num : (1/10^25:ℝ)<1/10^13)
    (fun i=>castRationalVector3 (d.plusOutput i)) (fun i=>castRationalVector3 (d.minusOutput i))
    hp hm hS hb htvalid.1 htvalid.2
  let ε : ℝ := 2*((6*10^14)*(1/10^25)+(1/10^40)/(1/10^25))+1/10^40
  have hJ : ‖rationalMatrixOperator d.jacobian-fderiv ℝ (actualShootingMap U hU) p₀‖≤ε := by
    simpa only [ε,U,hU,FivePathCertificateData.fieldBall,FivePathCertificateData.jacobian,fivePathRationalJacobian_operator,
      cast_projectedRationalCenter,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hJreal
  obtain ⟨hB,hdef,hres⟩ := rational_preconditioner_checks hBc hJc hyc
  norm_num only [Rat.cast_ofNat,Rat.cast_div,Rat.cast_one,Rat.cast_pow] at hB hdef hres
  obtain ⟨p,hpball,hroot,_⟩ := exists_actual_shooting_root_of_matrix_certificate
    hT hTmin hbudget hcenter hc (q:=⟨2/10^9,by positivity⟩)
    (r:=1/10^28) (η:=1/10^40) (ε:=ε) (β:=2) (q₀:=1/10^9) (ζ:=1/10^35)
    (by positivity) (by norm_num) (by norm_num)
    (by change (2/(10:ℝ)^9)<1; norm_num) (by norm_num)
    (castRationalVector3 d.centerOutput) (rationalMatrixOperator d.preconditioner)
    (rationalMatrixOperator d.jacobian) hy hJ hB
    (by convert! hdef using 1; norm_num) (by convert! hres using 1; norm_num)
    (by change (1/(10:ℝ)^9)+2*(ε+(6*10^14)*(1/10^28))≤2/10^9; dsimp [ε]; norm_num)
    (by change ((1/(10:ℝ)^35)+2*(1/10^40))+(2/10^9)*(1/10^28)≤1/10^28; norm_num)
  have hmom : (7000000:ℝ)*(1/10^28)<shootingFlow T hT.le T (shootingInitial p₀) 6 := by
    have he := checked_center_moment_margin hT.le hcenter hb hmomc
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using he
  have hgeometry := nearby_shooting_zero_yields_smooth_classical_FEF_escape hT hTmin hbudget
    hcenter hc (by norm_num : (1/10^28:ℝ)<1/10^13) hmom hpball hroot
  have hpL : 0<p 2 := by
    have hcoord := norm_le_pi_norm (p-p₀) 2
    change |p 2-p₀ 2|≤‖p-p₀‖ at hcoord
    have hdist : ‖p-p₀‖≤1/(10:ℝ)^28 := by
      have hh : dist p p₀≤1/(10:ℝ)^28 := hpball
      rwa [dist_eq_norm] at hh
    rw [hcenter] at hcoord
    have hlow := (abs_le.mp hcoord).1
    linarith
  exact ⟨p 2,hpL,hgeometry⟩

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.checked_fivePathCertificate_yields_smooth_classical_FEF_escape

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Complete five-path certificate audit passed for {checked} declarations."
