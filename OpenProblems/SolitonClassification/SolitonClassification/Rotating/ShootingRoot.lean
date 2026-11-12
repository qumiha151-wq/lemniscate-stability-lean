import SolitonClassification.Rotating.BanachRoot
import SolitonClassification.Rotating.Field
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Exact five-parameter shooting map and chain-rule interface. The local
ODE flow, its actual strict derivative on the required endpoint neighborhoods,
and all numerical enclosures remain explicit obligations. This file proves
neither an 8000-step enclosure nor the existence of the candidate orbit. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Metric
open scoped NNReal ContDiff
set_option backward.isDefEq.respectTransparency false

abbrev Parameters := Fin 5 → ℝ

/-- Parameters are (k0,p0,half-length,alpha,b); normalized state is
(k,v/8,p,q,b,theta). The phase line e is kept exactly fixed. -/
def shootingInitial (e : Fin 2 → ℝ) : Parameters →L[ℝ] State :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    (e 0/8) • ContinuousLinearMap.proj 3,ContinuousLinearMap.proj 1,
    e 1 • ContinuousLinearMap.proj 3,ContinuousLinearMap.proj 4,0]

def shootingLength : Parameters →L[ℝ] ℝ := ContinuousLinearMap.proj 2

def forwardEndpointInput (e : Fin 2 → ℝ) : Parameters →L[ℝ] (ℝ×State) :=
  shootingLength.prod (shootingInitial e)

def backwardEndpointInput (e : Fin 2 → ℝ) : Parameters →L[ℝ] (ℝ×State) :=
  (-shootingLength).prod (shootingInitial e)

/-- Converts normalized state differences back to physical support residuals,
with the fifth residual recording the actual angle increment. -/
def shootingProjection : State →L[ℝ] Parameters :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    (8:ℝ) • ContinuousLinearMap.proj 1,ContinuousLinearMap.proj 2,
    ContinuousLinearMap.proj 3,ContinuousLinearMap.proj 5]

def shootingTarget : Parameters := ![0,0,0,0,112*Real.pi/57]

def shootingMap (e : Fin 2 → ℝ) (Φ : ℝ×State → State) (c : Parameters) : Parameters :=
  shootingProjection (Φ (forwardEndpointInput e c)-Φ (backwardEndpointInput e c))+shootingTarget

def shootingDerivative (e : Fin 2 → ℝ) (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State)
    (c : Parameters) : Parameters →L[ℝ] Parameters :=
  shootingProjection.comp
    ((DΦ (forwardEndpointInput e c)).comp (forwardEndpointInput e)-
      (DΦ (backwardEndpointInput e c)).comp (backwardEndpointInput e))

theorem shootingInitial_apply (e : Fin 2 → ℝ) (c : Parameters) :
    shootingInitial e c=![c 0,c 3*e 0/8,c 1,c 3*e 1,c 4,0] := by
  ext i
  fin_cases i <;> simp [shootingInitial] <;> ring

theorem shootingProjection_apply (x : State) :
    shootingProjection x=![x 0,8*x 1,x 2,x 3,x 5] := by
  ext i
  fin_cases i <;> simp [shootingProjection]

/-- A true zero enforces exact support matching and the exact irrational
angle target, rather than matching a rounded decimal angle. -/
theorem shootingMap_eq_zero_iff (e : Fin 2 → ℝ) (Φ : ℝ×State → State) (c : Parameters) :
    shootingMap e Φ c=0 ↔
      Φ (forwardEndpointInput e c) 0=Φ (backwardEndpointInput e c) 0 ∧
      Φ (forwardEndpointInput e c) 1=Φ (backwardEndpointInput e c) 1 ∧
      Φ (forwardEndpointInput e c) 2=Φ (backwardEndpointInput e c) 2 ∧
      Φ (forwardEndpointInput e c) 3=Φ (backwardEndpointInput e c) 3 ∧
      Φ (forwardEndpointInput e c) 5-Φ (backwardEndpointInput e c) 5= -112*Real.pi/57 := by
  constructor
  · intro h
    have hh (i : Fin 5) := congrFun h i
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    have h3 := hh 3
    have h4 := hh 4
    simp [shootingMap,shootingProjection,shootingTarget] at h0 h1 h2 h3 h4
    exact ⟨sub_eq_zero.mp h0,by linarith,sub_eq_zero.mp h2,sub_eq_zero.mp h3,by linarith⟩
  · rintro ⟨h0,h1,h2,h3,h4⟩
    ext i
    fin_cases i <;> simp [shootingMap,shootingProjection,shootingTarget,h0,h1,h2,h3,h4]
    ring

/-- The operator uses the physical v row, whose scale is eight. -/
theorem shootingProjection_norm : ‖shootingProjection‖≤8 := by
  apply shootingProjection.opNorm_le_bound (by norm_num)
  intro x
  rw [pi_norm_le_iff_of_nonneg (by positivity),shootingProjection_apply]
  intro i
  fin_cases i
  · change |x 0|≤8*‖x‖
    linarith [coordinate_bound x 0,norm_nonneg x]
  · change |8*x 1|≤8*‖x‖
    rw [abs_mul,abs_of_pos (by norm_num : 0<(8:ℝ))]
    exact mul_le_mul_of_nonneg_left (coordinate_bound x 1) (by norm_num)
  · change |x 2|≤8*‖x‖
    linarith [coordinate_bound x 2,norm_nonneg x]
  · change |x 3|≤8*‖x‖
    linarith [coordinate_bound x 3,norm_nonneg x]
  · change |x 5|≤8*‖x‖
    linarith [coordinate_bound x 5,norm_nonneg x]

theorem shootingMap_hasStrictFDerivAt (e : Fin 2 → ℝ) (Φ : ℝ×State → State)
    (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State) (c : Parameters)
    (hplus : HasStrictFDerivAt Φ (DΦ (forwardEndpointInput e c)) (forwardEndpointInput e c))
    (hminus : HasStrictFDerivAt Φ (DΦ (backwardEndpointInput e c)) (backwardEndpointInput e c)) :
    HasStrictFDerivAt (shootingMap e Φ) (shootingDerivative e DΦ c) c := by
  exact ((shootingProjection.hasStrictFDerivAt.comp c
    ((hplus.comp c (forwardEndpointInput e).hasStrictFDerivAt).sub
      (hminus.comp c (backwardEndpointInput e).hasStrictFDerivAt))).add_const shootingTarget)

theorem shootingMap_hasFDerivAt (e : Fin 2 → ℝ) (Φ : ℝ×State → State)
    (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State) (c : Parameters)
    (hplus : HasFDerivAt Φ (DΦ (forwardEndpointInput e c)) (forwardEndpointInput e c))
    (hminus : HasFDerivAt Φ (DΦ (backwardEndpointInput e c)) (backwardEndpointInput e c)) :
    HasFDerivAt (shootingMap e Φ) (shootingDerivative e DΦ c) c := by
  exact ((shootingProjection.hasFDerivAt.comp c
    ((hplus.comp c (forwardEndpointInput e).hasFDerivAt).sub
      (hminus.comp c (backwardEndpointInput e).hasFDerivAt))).add_const shootingTarget)

def lengthDirection : Parameters := ![0,0,1,0,0]

theorem forward_lengthDirection (e : Fin 2 → ℝ) :
    forwardEndpointInput e lengthDirection=(1,0) := by
  apply Prod.ext
  · simp [forwardEndpointInput,shootingLength,lengthDirection]
  · ext i
    fin_cases i <;> simp [forwardEndpointInput,shootingInitial,lengthDirection]

theorem backward_lengthDirection (e : Fin 2 → ℝ) :
    backwardEndpointInput e lengthDirection=(-1,0) := by
  apply Prod.ext
  · simp [backwardEndpointInput,shootingLength,lengthDirection]
  · ext i
    fin_cases i <;> simp [backwardEndpointInput,shootingInitial,lengthDirection]

/-- Both endpoint time columns enter with a plus sign: differentiating the
negative endpoint time cancels the subtraction of the negative branch. -/
theorem shootingDerivative_length_column (e : Fin 2 → ℝ)
    (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State) (c : Parameters) :
    shootingDerivative e DΦ c lengthDirection=
      shootingProjection (DΦ (forwardEndpointInput e c) (1,0)+
        DΦ (backwardEndpointInput e c) (1,0)) := by
  simp only [shootingDerivative,ContinuousLinearMap.comp_apply,sub_apply,
    forward_lengthDirection,backward_lengthDirection]
  have he : ((-1:ℝ),(0:State))= -((1:ℝ),(0:State)) := by simp
  rw [he,map_neg,sub_neg_eq_add]

/-- Actual time-ODE differentiation identifies the joint derivative's time
column. No variational or endpoint matrix is assumed exact. -/
theorem flow_derivative_time_column {Φ : ℝ×State → State}
    {D : (ℝ×State) →L[ℝ] State} {t : ℝ} {x : State}
    (hD : HasFDerivAt Φ D (t,x))
    (hODE : HasDerivAt (fun s => Φ (s,x)) (field (Φ (t,x))) t) :
    D (1,0)=field (Φ (t,x)) := by
  have hp : HasDerivAt (fun s : ℝ => (s,x)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (hD.comp_hasDerivAt t hp).unique hODE

theorem shootingDerivative_length_column_of_ODE (e : Fin 2 → ℝ)
    (Φ : ℝ×State → State) (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State) (c : Parameters)
    (hplus : HasFDerivAt Φ (DΦ (forwardEndpointInput e c)) (forwardEndpointInput e c))
    (hminus : HasFDerivAt Φ (DΦ (backwardEndpointInput e c)) (backwardEndpointInput e c))
    (hODEplus : HasDerivAt (fun s => Φ (s,shootingInitial e c))
      (field (Φ (forwardEndpointInput e c))) (shootingLength c))
    (hODEminus : HasDerivAt (fun s => Φ (s,shootingInitial e c))
      (field (Φ (backwardEndpointInput e c))) (-shootingLength c)) :
    shootingDerivative e DΦ c lengthDirection=
      shootingProjection (field (Φ (forwardEndpointInput e c))+
        field (Φ (backwardEndpointInput e c))) := by
  rw [shootingDerivative_length_column,
    flow_derivative_time_column hplus hODEplus,
    flow_derivative_time_column hminus hODEminus]
  rfl

/-- This is an implication from actual analytic/enclosure bounds to a true
shooting zero. None of those bounds is discharged for the numerical candidate
by this generic interface. -/
theorem exists_unique_shooting_zero_of_certificate
    (e : Fin 2 → ℝ) (Φ : ℝ×State → State)
    (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State)
    (B J : Parameters →L[ℝ] Parameters) (p y : Parameters)
    {r η ε β H q₀ ζ : ℝ} (q : ℝ≥0)
    (hr : 0≤r) (hβ : 0≤β) (hH : 0≤H) (hq : q<1) (hq₀ : q₀<1)
    (hflow : ∀c∈closedBall p r,
      HasStrictFDerivAt Φ (DΦ (forwardEndpointInput e c)) (forwardEndpointInput e c) ∧
      HasStrictFDerivAt Φ (DΦ (backwardEndpointInput e c)) (backwardEndpointInput e c))
    (hvariation : ∀c∈closedBall p r,
      ‖shootingDerivative e DΦ c-shootingDerivative e DΦ p‖≤H*dist c p)
    (hzero : ‖y-shootingMap e Φ p‖≤η)
    (hJ : ‖J-shootingDerivative e DΦ p‖≤ε) (hB : ‖B‖≤β)
    (hmatrix : ‖ContinuousLinearMap.id ℝ Parameters-B.comp J‖≤q₀)
    (hresidual : ‖B y‖≤ζ) (hcontraction : q₀+β*(ε+H*r)≤(q:ℝ))
    (hself : (ζ+β*η)+(q:ℝ)*r≤r) :
    ∃c∈closedBall p r, shootingMap e Φ c=0 ∧
      ∀c'∈closedBall p r, shootingMap e Φ c'=0 → c'=c :=
  exists_unique_zero_of_strict_certificate (shootingMap e Φ) (shootingDerivative e DΦ)
    B J p y q hr hβ hH hq hq₀
    (fun c hc => shootingMap_hasStrictFDerivAt e Φ DΦ c (hflow c hc).1 (hflow c hc).2)
    hvariation hzero hJ hB hmatrix hresidual hcontraction hself

/-- A genuine Hessian bound can supply the derivative-variation hypothesis.
The bound concerns the derivative of the actual shooting derivative, not
the derivative of a numerical Taylor polynomial. -/
theorem exists_unique_shooting_zero_of_hessian_certificate
    (e : Fin 2 → ℝ) (Φ : ℝ×State → State)
    (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State)
    (DD : Parameters → Parameters →L[ℝ] (Parameters →L[ℝ] Parameters))
    (B J : Parameters →L[ℝ] Parameters) (p y : Parameters)
    {r η ε β H q₀ ζ : ℝ} (q : ℝ≥0)
    (hr : 0≤r) (hβ : 0≤β) (hH : 0≤H) (hq : q<1) (hq₀ : q₀<1)
    (hflow : ∀c∈closedBall p r,
      HasStrictFDerivAt Φ (DΦ (forwardEndpointInput e c)) (forwardEndpointInput e c) ∧
      HasStrictFDerivAt Φ (DΦ (backwardEndpointInput e c)) (backwardEndpointInput e c))
    (hDD : ∀c∈closedBall p r, HasFDerivAt (shootingDerivative e DΦ) (DD c) c)
    (hHessian : ∀c∈closedBall p r, ‖DD c‖≤H)
    (hzero : ‖y-shootingMap e Φ p‖≤η)
    (hJ : ‖J-shootingDerivative e DΦ p‖≤ε) (hB : ‖B‖≤β)
    (hmatrix : ‖ContinuousLinearMap.id ℝ Parameters-B.comp J‖≤q₀)
    (hresidual : ‖B y‖≤ζ) (hcontraction : q₀+β*(ε+H*r)≤(q:ℝ))
    (hself : (ζ+β*η)+(q:ℝ)*r≤r) :
    ∃c∈closedBall p r, shootingMap e Φ c=0 ∧
      ∀c'∈closedBall p r, shootingMap e Φ c'=0 → c'=c :=
  exists_unique_shooting_zero_of_certificate e Φ DΦ B J p y q hr hβ hH hq hq₀
    hflow (derivative_variation_of_second_derivative (shootingDerivative e DΦ) DD hr hDD hHessian)
    hzero hJ hB hmatrix hresidual hcontraction hself

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating shooting root audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating shooting root audit passed for {count} declarations."
