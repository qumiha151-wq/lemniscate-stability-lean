import CentroidEscape.FivePathRationalData

namespace CentroidEscape.MetricStability
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

/-- Exactly 751 finite tables: 750 checked steps and the final endpoint. -/
structure FiniteShootingPath where
  table : Fin 751 → FixedTaylorState

def FiniteShootingPath.stage (d : FiniteShootingPath) (n : ℕ) : FixedTaylorState :=
  d.table ⟨min n 750,by omega⟩

def rationalShootingInitial (p : RationalVector3) : Fin 7 → ℚ :=
  ![p 0,0,0,1/4,p 1/16,0,0]

def FiniteShootingPath.endpoint (d : FiniteShootingPath) (S : ℕ) : BallVector :=
  order60EndpointBalls S 750 d.stage

def FiniteShootingPath.Valid (d : FiniteShootingPath) (S : ℕ) (h : ℚ)
    (p : RationalVector3) : Prop :=
  (∀ j : Fin 750, checkOrderTaylorData S 60 (d.stage j.val)=true) ∧
  (∀ j : Fin 750, ∀ i : Fin 7,
    (d.stage (j.val+1)).coefficient 0 i=(evaluateFixedTaylorOrder S 60 h (d.stage j.val))[i.val]) ∧
  (∀ j : Fin 750, checkBallCanonicalMargin
    (fun i=>((d.stage j.val).coefficient 0 i).toRational S)=true) ∧
  (∀ i : Fin 7, |rationalShootingInitial p i-(((d.stage 0).coefficient 0 i).toRational S).center|≤
    (((d.stage 0).coefficient 0 i).toRational S).radius) ∧
  checkProjectedRadius (d.endpoint S) (1/10^40)=true

instance (d : FiniteShootingPath) (S : ℕ) (h : ℚ) (p : RationalVector3) :
    Decidable (d.Valid S h p) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _ ∧ _ ∧ _)))

def FiniteShootingPath.check (d : FiniteShootingPath) (S : ℕ) (h : ℚ)
    (p : RationalVector3) : Bool := decide (d.Valid S h p)

theorem FiniteShootingPath.initial_contains {d : FiniteShootingPath} {S : ℕ} {h : ℚ}
    {p : RationalVector3} (hv : d.Valid S h p) :
    ∀ i, ((d.stage 0).coefficient 0 i).Contains S (shootingInitial (castRationalVector3 p) i) := by
  intro i
  have hq := hv.2.2.2.1 i
  have hc : |(rationalShootingInitial p i:ℝ)-
      ((((d.stage 0).coefficient 0 i).toRational S).center:ℝ)|≤
      ((((d.stage 0).coefficient 0 i).toRational S).radius:ℝ) := by exact_mod_cast hq
  have he : (rationalShootingInitial p i:ℝ)=shootingInitial (castRationalVector3 p) i := by
    fin_cases i <;> simp [rationalShootingInitial,shootingInitial,castRationalVector3]
  rw [he] at hc
  exact hc

theorem FiniteShootingPath.checked_inner {d : FiniteShootingPath} {S : ℕ} (hS : 0<S)
    {h : ℚ} (hh : 0≤h) (hhmax : h≤1/100) {p : RationalVector3}
    (hcheck : d.check S h p=true) :
    ∀ t∈Icc 0 ((750:ℝ)*(h:ℝ)),
      shootingFlow ((750:ℝ)*(h:ℝ))
        (mul_nonneg (by norm_num) (Rat.cast_nonneg.mpr hh)) t (shootingInitial (castRationalVector3 p))
        ∈innerWeightedTube := by
  have hv : d.Valid S h p := of_decide_eq_true hcheck
  exact (checked_order60_shootingFlow hS (by norm_num) le_rfl hh hhmax d.stage
    (fun j hj=>hv.1 ⟨j,hj⟩) (fun j hj=>hv.2.1 ⟨j,hj⟩)
    (fun j hj=>hv.2.2.1 ⟨j,hj⟩) (initial_contains hv)).1

theorem FiniteShootingPath.checked_endpoint {d : FiniteShootingPath} {S : ℕ} (hS : 0<S)
    {h : ℚ} (hh : 0≤h) (hhmax : h≤1/100) {p : RationalVector3}
    (hcheck : d.check S h p=true) (hp : (p 2:ℝ)=(750:ℝ)*(h:ℝ))
    {U : ℝ} (hU : 0≤U) (horizon : (750:ℝ)*(h:ℝ)≤U) :
    ∀ i, (d.endpoint S i).Contains
      (shootingFlow U hU (p 2) (shootingInitial (castRationalVector3 p)) i) := by
  have hv : d.Valid S h p := of_decide_eq_true hcheck
  exact checked_order60_probe_endpoint hS (by norm_num) le_rfl hh hhmax d.stage
    (fun j hj=>hv.1 ⟨j,hj⟩) (fun j hj=>hv.2.1 ⟨j,hj⟩)
    (fun j hj=>hv.2.2.1 ⟨j,hj⟩) (initial_contains hv) hp hU horizon

theorem FiniteShootingPath.checked_output {d : FiniteShootingPath} {S : ℕ} (hS : 0<S)
    {h : ℚ} (hh : 0≤h) (hhmax : h≤1/100) {p : RationalVector3}
    (hcheck : d.check S h p=true) (hp : (p 2:ℝ)=(750:ℝ)*(h:ℝ))
    {U : ℝ} (hU : 0≤U) (horizon : (750:ℝ)*(h:ℝ)≤U) :
    ‖castRationalVector3 (projectedRationalCenter (d.endpoint S))-
      actualShootingMap U hU (castRationalVector3 p)‖≤(1/10^40:ℝ) := by
  have hv : d.Valid S h p := of_decide_eq_true hcheck
  have he := checkProjectedRadius_sound hv.2.2.2.2
    (checked_endpoint hS hh hhmax hcheck hp hU horizon)
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,
    actualShootingMap,castRationalVector3] using he

end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.FiniteShootingPath.checked_output

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
  logInfo m!"Finite shooting path audit passed for {checked} declarations."
