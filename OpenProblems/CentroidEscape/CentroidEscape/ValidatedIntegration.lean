import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Util.CollectAxioms

/-!
# Propagating local integration errors along actual ODE solutions

This module derives the global error from differential equations and local
endpoint defects. It does not assume the global error recurrence. The local
Taylor-majorant theorem, enclosure of the exact discrete iterates by rational
interval arithmetic, and the tube continuation bootstrap remain separate
obligations. In particular, this is not an end-to-end certificate verifier.
-/

namespace CentroidEscape
noncomputable section
set_option maxRecDepth 4096
open Set Real
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded globally Lipschitz field admits an actual solution on any
specified finite interval. This can be applied to a coordinate-clipped field
before proving that the solution stays in the unclipped region. -/
theorem exists_ode_on_finite_interval [CompleteSpace E]
    (f : E → E) (K M : ℝ≥0) (x : E) (T : ℝ) (hT : 0 ≤ T)
    (hLip : LipschitzWith K f) (hbound : ∀ y, ‖f y‖ ≤ M) :
    ∃ z : ℝ → E, z 0 = x ∧
      ∀ t ∈ Icc 0 T, HasDerivAt z (f (z t)) t := by
  let t₀ : Icc (-1 : ℝ) (T+1) := ⟨0, by constructor <;> linarith⟩
  let radius : ℝ≥0 := ⟨(M : ℝ)*(T+1), by positivity⟩
  have hp : IsPicardLindelof (fun _ => f) t₀ x radius 0 M K := by
    apply IsPicardLindelof.of_time_independent
    · intro y _; exact hbound y
    · exact hLip.lipschitzOnWith
    · change (M : ℝ) * max (T+1-0) (0-(-1)) ≤ (M : ℝ)*(T+1)-0
      rw [sub_zero, sub_neg_eq_add, zero_add, sub_zero,
        max_eq_left (by linarith : (1 : ℝ) ≤ T+1)]
  obtain ⟨z, hz0, hz⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨z, hz0, ?_⟩
  intro t ht
  have ht' : t ∈ Ioo (-1 : ℝ) (T+1) := by constructor <;> linarith [ht.1, ht.2]
  exact (hz t (Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)

omit [NormedSpace ℝ E] in
/-- A geometric majorant on the actual series terms gives the truncation
error. The error estimate itself is not a hypothesis. -/
theorem series_truncation_error
    (a : ℕ → E) (value : E) (N : ℕ) (M r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hs : HasSum a value)
    (hbound : ∀ n ≥ N+1, ‖a n‖ ≤ M*r^n) :
    ‖value - ∑ n ∈ Finset.range (N+1), a n‖ ≤ M*r^(N+1)/(1-r) := by
  have ht := (hasSum_nat_add_iff' (N+1)).mpr hs
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (M*r^(N+1))
  have hb : ∀ n, ‖a (n+(N+1))‖ ≤ (M*r^(N+1))*r^n := by
    intro n
    calc
      ‖a (n+(N+1))‖ ≤ M*r^(n+(N+1)) := hbound _ (by omega)
      _ = (M*r^(N+1))*r^n := by rw [pow_add]; ring
  simpa only [div_eq_mul_inv] using ht.norm_le_of_bounded hg hb

/-- The coefficient bound used in the analytic majorant proof yields the
published Taylor tail. Establishing these coefficients from the polynomial
ODE and identifying their sum with its local solution remain obligations. -/
theorem taylor_tail_of_coefficients
    (a : ℕ → E) (value : E) (N : ℕ) (h : ℝ)
    (hh : 0 ≤ h) (hhsmall : 12*h < 1)
    (hs : HasSum (fun n => h^n • a n) value)
    (hcoeff : ∀ n ≥ 1, ‖a n‖ ≤ (12 : ℝ)^n/3) :
    ‖value - ∑ n ∈ Finset.range (N+1), h^n • a n‖
      ≤ (12*h)^(N+1)/(3*(1-12*h)) := by
  have hb : ∀ n ≥ N+1, ‖h^n • a n‖ ≤ (1/3 : ℝ)*(12*h)^n := by
    intro n hn
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hh n)]
    calc
      h^n*‖a n‖ ≤ h^n*((12 : ℝ)^n/3) :=
        mul_le_mul_of_nonneg_left (hcoeff n (by omega)) (pow_nonneg hh n)
      _ = (1/3 : ℝ)*(12*h)^n := by rw [mul_pow]; ring
  have ht := series_truncation_error (fun n => h^n • a n) value N (1/3) (12*h)
    (by positivity) hhsmall hs hb
  simpa only [div_eq_mul_inv, mul_inv_rev, one_mul, mul_comm, mul_left_comm,
    mul_assoc] using ht

/-- One integration step: actual ODE derivatives and a local endpoint defect
imply an error recurrence, via Gronwall inside the tube. -/
theorem ode_step_error
    (f : E → E) (S : Set E) (K : ℝ≥0) (a b : ℝ) (hab : a ≤ b)
    (z y : ℝ → E) (c next : E) (τ : ℝ)
    (hLip : LipschitzOnWith K f S)
    (hz : ContinuousOn z (Icc a b))
    (hz' : ∀ t ∈ Ico a b, HasDerivAt z (f (z t)) t)
    (hzS : ∀ t ∈ Ico a b, z t ∈ S)
    (hy : ContinuousOn y (Icc a b))
    (hy' : ∀ t ∈ Ico a b, HasDerivAt y (f (y t)) t)
    (hyS : ∀ t ∈ Ico a b, y t ∈ S)
    (hy0 : y a = c) (htail : dist (y b) next ≤ τ) :
    dist (z b) next ≤ dist (z a) c * exp ((K : ℝ) * (b-a)) + τ := by
  have hcompare := dist_le_of_trajectories_ODE_of_mem
    (v := fun _ => f) (s := fun _ => S)
    (fun _ _ => hLip) hz (fun t ht => (hz' t ht).hasDerivWithinAt) hzS
    hy (fun t ht => (hy' t ht).hasDerivWithinAt) hyS
    (δ := dist (z a) c) (by rw [hy0]) b ⟨hab, le_rfl⟩
  exact (dist_triangle (z b) (y b) next).trans (add_le_add hcompare htail)

/-- Error propagation for a finite sequence of local reference solutions.
The comparison factor is deduced from the ODE on every step. -/
theorem ode_grid_error
    (f : E → E) (S : Set E) (K : ℝ≥0)
    (h τ : ℝ) (hh : 0 ≤ h) (hτ : 0 ≤ τ) (N : ℕ)
    (z : ℝ → E) (c : ℕ → E) (y : ℕ → ℝ → E)
    (hLip : LipschitzOnWith K f S) (hinit : z 0 = c 0)
    (hz : ∀ j < N, ContinuousOn z (Icc (j*h) ((j+1)*h)))
    (hz' : ∀ j < N, ∀ t ∈ Ico (j*h) ((j+1)*h),
      HasDerivAt z (f (z t)) t)
    (hzS : ∀ j < N, ∀ t ∈ Ico (j*h) ((j+1)*h), z t ∈ S)
    (hy : ∀ j < N, ContinuousOn (y j) (Icc (j*h) ((j+1)*h)))
    (hy' : ∀ j < N, ∀ t ∈ Ico (j*h) ((j+1)*h),
      HasDerivAt (y j) (f (y j t)) t)
    (hyS : ∀ j < N, ∀ t ∈ Ico (j*h) ((j+1)*h), y j t ∈ S)
    (hy0 : ∀ j < N, y j (j*h) = c j)
    (htail : ∀ j < N, dist (y j ((j+1)*h)) (c (j+1)) ≤ τ) :
    ∀ n ≤ N, dist (z (n*h)) (c n) ≤ n * τ * exp ((K : ℝ) * (n*h)) := by
  intro n hn
  induction n with
  | zero => simp [hinit]
  | succ n ih =>
    have hnN : n < N := Nat.lt_of_succ_le hn
    have hind := ih (Nat.le_of_lt hnN)
    have hstep := ode_step_error f S K (n*h) ((n+1)*h) (by nlinarith)
      z (y n) (c n) (c (n+1)) τ hLip (hz n hnN) (hz' n hnN)
      (hzS n hnN) (hy n hnN) (hy' n hnN) (hyS n hnN) (hy0 n hnN)
      (htail n hnN)
    have htime : (n+1 : ℝ)*h-n*h = h := by ring
    rw [htime] at hstep
    have hmul : exp ((K : ℝ)*(n*h)) * exp ((K : ℝ)*h) =
        exp ((K : ℝ)*((n+1)*h)) := by rw [← exp_add]; congr 1; ring
    have hexp : 1 ≤ exp ((K : ℝ)*((n+1)*h)) := by
      apply one_le_exp
      positivity
    calc
      dist (z ((n.succ : ℝ)*h)) (c n.succ)
          ≤ dist (z (n*h)) (c n) * exp ((K : ℝ)*h) + τ := by
              simpa only [Nat.cast_succ] using hstep
      _ ≤ (n*τ*exp ((K : ℝ)*(n*h))) * exp ((K : ℝ)*h) + τ :=
        add_le_add (mul_le_mul_of_nonneg_right hind (exp_pos _).le) le_rfl
      _ = n*τ*exp ((K : ℝ)*((n+1)*h)) + τ := by rw [mul_assoc, hmul]
      _ ≤ n*τ*exp ((K : ℝ)*((n+1)*h)) + τ*exp ((K : ℝ)*((n+1)*h)) :=
        add_le_add le_rfl (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hexp hτ)
      _ = (n.succ : ℝ)*τ*exp ((K : ℝ)*((n.succ : ℝ)*h)) := by
        rw [Nat.cast_succ]; ring

/-- The exact worst-case local tail at order 160 and step 1/100. -/
def integrationTail : ℝ := (12*(1/100 : ℝ))^161 / (3*(1-12*(1/100 : ℝ)))

theorem integrationTail_nonneg : 0 ≤ integrationTail := by
  norm_num [integrationTail]

/-- Kernel-checked transcendental and rational arithmetic for the published
global budget. This does not trust an Arb decimal approximation of exp(60). -/
theorem integration_budget :
    750 * integrationTail * exp 60 < 1/(10 : ℝ)^118 := by
  have happrox := exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  have hone : exp 1 ≤ (11/4 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at happrox
    linarith
  have h60 : exp 60 ≤ (11/4 : ℝ)^60 := by
    calc
      exp 60 = (exp 1)^60 := by simpa using (exp_nat_mul 1 60)
      _ ≤ (11/4 : ℝ)^60 := pow_le_pow_left₀ (exp_pos _).le hone 60
  calc
    750*integrationTail*exp 60 ≤ 750*integrationTail*(11/4 : ℝ)^60 :=
      mul_le_mul_of_nonneg_left h60 (mul_nonneg (by norm_num) integrationTail_nonneg)
    _ < 1/(10 : ℝ)^118 := by norm_num [integrationTail]

/-- Applying the grid estimate with 750 steps, Lipschitz bound 8 and step
size at most 1/100 reaches the strict numerical budget. -/
theorem error_lt_integration_budget
    (error h : ℝ) (hh : h ≤ 1/100)
    (he : error ≤ 750*integrationTail*exp (8*(750*h))) :
    error < 1/(10 : ℝ)^118 := by
  apply lt_of_le_of_lt he
  calc
    750*integrationTail*exp (8*(750*h)) ≤ 750*integrationTail*exp 60 := by
      apply mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (by linarith))
        (mul_nonneg (by norm_num) integrationTail_nonneg)
    _ < 1/(10 : ℝ)^118 := integration_budget

end
end CentroidEscape

#print axioms CentroidEscape.ode_grid_error
#print axioms CentroidEscape.integration_budget

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
  unless checked > 0 do throwError "No integration declarations checked"
  logInfo m!"Validated integration audit passed for {checked} declarations."
