import CentroidEscape.Reparametrization
import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual global parameter flow is an invertible increasing lift

All flow identities and continuity are derived from the previously established
existence theorem and ODE uniqueness. Spatial differentiability and invariance
of the arclength integral are separate obligations.
-/

namespace CentroidEscape
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

structure ParameterFieldData where
  field : ℝ → ℝ
  K : ℝ≥0
  M : ℝ≥0
  lip : LipschitzWith K field
  bound : ∀ x, ‖field x‖ ≤ M

def parameterFlow (G : ParameterFieldData) (t x : ℝ) : ℝ :=
  (exists_unique_global_scalar_flow G.lip G.bound x).exists.choose t

lemma parameterFlow_zero (G : ParameterFieldData) (x : ℝ) :
    parameterFlow G 0 x = x :=
  (exists_unique_global_scalar_flow G.lip G.bound x).exists.choose_spec.1

lemma parameterFlow_derivative (G : ParameterFieldData) (x t : ℝ) :
    HasDerivAt (fun s => parameterFlow G s x) (G.field (parameterFlow G t x)) t :=
  (exists_unique_global_scalar_flow G.lip G.bound x).exists.choose_spec.2 t

lemma parameterFlow_time_continuous (G : ParameterFieldData) (x : ℝ) :
    Continuous (fun t => parameterFlow G t x) :=
  continuous_iff_continuousAt.mpr fun t => (parameterFlow_derivative G x t).continuousAt

lemma parameterFlow_unique (G : ParameterFieldData) {f : ℝ → ℝ} {x : ℝ}
    (h0 : f 0 = x) (hf : ∀ t, HasDerivAt f (G.field (f t)) t) :
    f = fun t => parameterFlow G t x := by
  apply ODE_solution_unique_univ (v := fun _ => G.field) (s := fun _ => univ)
    (fun _ => G.lip.lipschitzOnWith)
    (fun t => ⟨hf t, mem_univ _⟩)
    (fun t => ⟨parameterFlow_derivative G x t, mem_univ _⟩)
  exact h0.trans (parameterFlow_zero G x).symm

theorem parameterFlow_add (G : ParameterFieldData) (s t x : ℝ) :
    parameterFlow G (s+t) x = parameterFlow G s (parameterFlow G t x) := by
  have hh : (fun r => parameterFlow G (r+t) x) =
      fun r => parameterFlow G r (parameterFlow G t x) := by
    apply parameterFlow_unique G
    · simp
    · intro r
      convert! (parameterFlow_derivative G x (r+t)).comp r
        ((hasDerivAt_id r).add_const t) using 1
      simp
  exact congrFun hh s

theorem parameterFlow_inverse (G : ParameterFieldData) (t x : ℝ) :
    parameterFlow G (-t) (parameterFlow G t x) = x := by
  rw [← parameterFlow_add, neg_add_cancel, parameterFlow_zero]

theorem parameterFlow_bijective (G : ParameterFieldData) (t : ℝ) :
    Function.Bijective (parameterFlow G t) := by
  constructor
  · intro x y h
    have hh := congrArg (parameterFlow G (-t)) h
    simpa only [parameterFlow_inverse] using hh
  · intro y
    refine ⟨parameterFlow G (-t) y, ?_⟩
    simpa using parameterFlow_inverse G (-t) y

theorem parameterFlow_period_lift (G : ParameterFieldData) {P : ℝ}
    (hp : Function.Periodic G.field P) (t x : ℝ) :
    parameterFlow G t (x+P) = parameterFlow G t x + P := by
  have hh : (fun r => parameterFlow G r x + P) =
      fun r => parameterFlow G r (x+P) := by
    apply parameterFlow_unique G
    · rw [parameterFlow_zero]
    · intro r
      rw [hp]
      exact (parameterFlow_derivative G x r).add_const P
  exact (congrFun hh t).symm

theorem parameterFlow_strictMono (G : ParameterFieldData) (t : ℝ) :
    StrictMono (parameterFlow G t) := by
  intro x y hxy
  by_contra h
  have hle : parameterFlow G t y - parameterFlow G t x ≤ 0 := by linarith
  have hpos : 0 ≤ parameterFlow G 0 y - parameterFlow G 0 x := by
    rw [parameterFlow_zero, parameterFlow_zero]
    linarith
  have hc : Continuous (fun r => parameterFlow G r y - parameterFlow G r x) :=
    (parameterFlow_time_continuous G y).sub (parameterFlow_time_continuous G x)
  obtain ⟨r, hr⟩ := intermediate_value_univ t 0 hc ⟨hle, hpos⟩
  have heq : parameterFlow G r y = parameterFlow G r x := sub_eq_zero.mp hr
  exact hxy.ne' ((parameterFlow_bijective G r).1 heq)

lemma scalar_solution_distance_forward {g : ℝ → ℝ} {K : ℝ≥0}
    (hlip : LipschitzWith K g) {f h : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (g (f t)) t)
    (hh : ∀ t, HasDerivAt h (g (h t)) t) {t : ℝ} (ht : 0 ≤ t) :
    dist (f t) (h t) ≤ dist (f 0) (h 0) * Real.exp ((K : ℝ)*t) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun r => (hf r).continuousAt
  have hhc : Continuous h := continuous_iff_continuousAt.mpr fun r => (hh r).continuousAt
  have hb := dist_le_of_trajectories_ODE (v := fun _ => g)
    (a := 0) (b := t) (fun _ => hlip) hfc.continuousOn
    (fun r _ => (hf r).hasDerivWithinAt) hhc.continuousOn
    (fun r _ => (hh r).hasDerivWithinAt) (δ := dist (f 0) (h 0)) le_rfl t ⟨ht, le_rfl⟩
  simpa using hb

lemma scalar_solution_distance {g : ℝ → ℝ} {K : ℝ≥0}
    (hlip : LipschitzWith K g) {f h : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (g (f t)) t)
    (hh : ∀ t, HasDerivAt h (g (h t)) t) (t : ℝ) :
    dist (f t) (h t) ≤ dist (f 0) (h 0) * Real.exp ((K : ℝ)*|t|) := by
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht] using scalar_solution_distance_forward hlip hf hh ht
  · have hfd : ∀ r, HasDerivAt (fun s => f (-s)) (-(g (f (-r)))) r := by
      intro r
      convert! (hf (-r)).comp r (hasDerivAt_id r).neg using 1
      simp
    have hhd : ∀ r, HasDerivAt (fun s => h (-s)) (-(g (h (-r)))) r := by
      intro r
      convert! (hh (-r)).comp r (hasDerivAt_id r).neg using 1
      simp
    have hb := scalar_solution_distance_forward hlip.neg hfd hhd
      (show 0 ≤ -t by linarith)
    simpa [abs_of_neg (lt_of_not_ge ht)] using hb

theorem parameterFlow_distance (G : ParameterFieldData) (t x y : ℝ) :
    dist (parameterFlow G t x) (parameterFlow G t y) ≤
      dist x y * Real.exp ((G.K : ℝ)*|t|) := by
  simpa only [parameterFlow_zero] using scalar_solution_distance G.lip
    (parameterFlow_derivative G x) (parameterFlow_derivative G y) t

theorem parameterFlow_lipschitz (G : ParameterFieldData) (t : ℝ) :
    LipschitzWith ⟨Real.exp ((G.K : ℝ)*|t|), (Real.exp_pos _).le⟩ (parameterFlow G t) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  change dist (parameterFlow G t x) (parameterFlow G t y) ≤
    Real.exp ((G.K : ℝ)*|t|) * dist x y
  simpa only [mul_comm] using parameterFlow_distance G t x y

def parameterFlowHomeomorph (G : ParameterFieldData) (t : ℝ) : ℝ ≃ₜ ℝ where
  toFun := parameterFlow G t
  invFun := parameterFlow G (-t)
  left_inv := parameterFlow_inverse G t
  right_inv := by intro x; simpa using parameterFlow_inverse G (-t) x
  continuous_toFun := (parameterFlow_lipschitz G t).continuous
  continuous_invFun := (parameterFlow_lipschitz G (-t)).continuous

lemma parameterFlow_coe_periodic (G : ParameterFieldData) {P : ℝ}
    (hp : Function.Periodic G.field P) (t : ℝ) :
    Function.Periodic (fun x => (parameterFlow G t x : AddCircle P)) P := by
  intro x
  dsimp only
  rw [parameterFlow_period_lift G hp]
  exact AddCircle.coe_add_period P _

def circleParameterFlow (G : ParameterFieldData) {P : ℝ}
    (hp : Function.Periodic G.field P) (t : ℝ) : AddCircle P → AddCircle P :=
  (parameterFlow_coe_periodic G hp t).lift

lemma circleParameterFlow_coe (G : ParameterFieldData) {P : ℝ}
    (hp : Function.Periodic G.field P) (t x : ℝ) :
    circleParameterFlow G hp t (x : AddCircle P) = (parameterFlow G t x : AddCircle P) := rfl

lemma circleParameterFlow_continuous (G : ParameterFieldData) {P : ℝ}
    (hp : Function.Periodic G.field P) (t : ℝ) : Continuous (circleParameterFlow G hp t) := by
  exact ((AddCircle.continuous_mk' P).comp (parameterFlow_lipschitz G t).continuous).quotient_liftOn' _

theorem circleParameterFlow_inverse (G : ParameterFieldData) {P : ℝ}
    (hp : Function.Periodic G.field P) (t : ℝ) (x : AddCircle P) :
    circleParameterFlow G hp (-t) (circleParameterFlow G hp t x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H x => simp only [circleParameterFlow_coe, parameterFlow_inverse]

/-- The quotient map is genuinely invertible and continuous in both directions,
not merely a family of individually chosen parameter trajectories. -/
def circleParameterHomeomorph (G : ParameterFieldData) {P : ℝ}
    (hp : Function.Periodic G.field P) (t : ℝ) : AddCircle P ≃ₜ AddCircle P where
  toFun := circleParameterFlow G hp t
  invFun := circleParameterFlow G hp (-t)
  left_inv := circleParameterFlow_inverse G hp t
  right_inv := by intro x; simpa using circleParameterFlow_inverse G hp (-t) x
  continuous_toFun := circleParameterFlow_continuous G hp t
  continuous_invFun := circleParameterFlow_continuous G hp (-t)

/-- Bounded/Lipschitz data obtained from the actual periodic polynomial ODE. -/
def profileParameterData {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) : ParameterFieldData where
  field := parameterField q
  K := (parameterField_bounded_lipschitz hq hp hP).choose
  M := (parameterField_bounded_lipschitz hq hp hP).choose_spec.choose
  lip := (parameterField_bounded_lipschitz hq hp hP).choose_spec.choose_spec.1
  bound := (parameterField_bounded_lipschitz hq hp hP).choose_spec.choose_spec.2

lemma profileParameterData_periodic {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) :
    Function.Periodic (profileParameterData hq hp hP).field P := by
  intro s
  simp only [profileParameterData, parameterField, hp s]

/-- A circle homeomorphism for every logarithmic time of the actual profile. -/
def profileCircleHomeomorph {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (τ : ℝ) : AddCircle P ≃ₜ AddCircle P :=
  circleParameterHomeomorph (profileParameterData hq hp hP)
    (profileParameterData_periodic hq hp hP) τ

/-- Actual physical-time lift, now selected coherently in the initial parameter. -/
def profileParameterLift {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (t s : ℝ) : ℝ :=
  parameterFlow (profileParameterData hq hp hP) (logarithmicTime t) s

theorem profileParameterLift_derivative {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun r => profileParameterLift hq hp hP r s)
      (parameterField q (profileParameterLift hq hp hP t s) / expanderRadius t ^ 4) t := by
  have hh := (parameterFlow_derivative (profileParameterData hq hp hP) s
    (logarithmicTime t)).comp t (logarithmicTime_derivative ht)
  convert! hh using 1
  simp [profileParameterLift, profileParameterData, div_eq_mul_inv]

theorem coherent_reparametrized_vector_FEF {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1)
    (hp : Function.Periodic q P) (hP : P ≠ 0) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun r => expandingCurve q r (profileParameterLift hq hp hP r s))
      ((-scaledForce q (expanderRadius t)
        (expanderRadius t * profileParameterLift hq hp hP t s)) •
        normal (q (profileParameterLift hq hp hP t s))) t :=
  reparametrized_trajectory_derivative hq hu ht
    (profileParameterLift_derivative hq hp hP ht s)

end
end CentroidEscape

#print axioms CentroidEscape.parameterFlow_strictMono
#print axioms CentroidEscape.parameterFlowHomeomorph
#print axioms CentroidEscape.profileCircleHomeomorph
#print axioms CentroidEscape.coherent_reparametrized_vector_FEF

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Centroid parameter-flow audit passed for {checked} declarations."
