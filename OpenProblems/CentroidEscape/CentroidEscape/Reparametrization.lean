import CentroidEscape.Geometry
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Existence of the scalar parameter flow

Bounded globally Lipschitz autonomous fields have genuine global solutions.
The construction below obtains solutions on arbitrarily large intervals by
Picard--Lindelof and glues them using uniqueness. Existence is a conclusion.
-/

namespace CentroidEscape
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

theorem bounded_lipschitz_interval_solution {g : ℝ → ℝ} {K M : ℝ≥0}
    (hlip : LipschitzWith K g) (hbound : ∀ x, ‖g x‖ ≤ M)
    (x₀ : ℝ) (T : ℝ≥0) :
    ∃ f : ℝ → ℝ, f 0 = x₀ ∧
      ∀ t ∈ Ioo (-(T : ℝ)) (T : ℝ), HasDerivAt f (g (f t)) t := by
  let t₀ : Icc (-(T : ℝ)) (T : ℝ) := ⟨0, by simp⟩
  have hp : IsPicardLindelof (fun _ => g) t₀ x₀ (M*T) 0 M K := by
    refine ⟨fun _ _ => hlip.lipschitzOnWith, fun _ _ => continuousOn_const,
      fun _ _ x _ => hbound x, ?_⟩
    simp [t₀]
  obtain ⟨f, h0, hf⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨f, h0, fun t ht => ?_⟩
  exact (hf t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

lemma scalar_interval_solutions_agree {g : ℝ → ℝ} {K : ℝ≥0}
    (hlip : LipschitzWith K g) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {f h : ℝ → ℝ}
    (hf : ∀ t ∈ Ioo (-A) A, HasDerivAt f (g (f t)) t)
    (hh : ∀ t ∈ Ioo (-B) B, HasDerivAt h (g (h t)) t)
    (h0 : f 0 = h 0) {t : ℝ} (htA : |t| < A) (htB : |t| < B) : f t = h t := by
  have hm : 0 < min A B := lt_min hA hB
  have subA : Ioo (-(min A B)) (min A B) ⊆ Ioo (-A) A := by
    intro x hx
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hx.1,
      lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have subB : Ioo (-(min A B)) (min A B) ⊆ Ioo (-B) B := by
    intro x hx
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hx.1,
      lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
  exact ODE_solution_unique_of_mem_Ioo (v := fun _ => g) (s := fun _ => univ)
    (fun _ _ => hlip.lipschitzOnWith) ⟨neg_neg_of_pos hm, hm⟩
    (fun x hx => ⟨hf x (subA hx), mem_univ _⟩)
    (fun x hx => ⟨hh x (subB hx), mem_univ _⟩) h0
    (abs_lt.mp (lt_min htA htB))

/-- A real bounded globally Lipschitz vector field admits a unique global
solution through each initial point. -/
theorem exists_unique_global_scalar_flow {g : ℝ → ℝ} {K M : ℝ≥0}
    (hlip : LipschitzWith K g) (hbound : ∀ x, ‖g x‖ ≤ M) (x₀ : ℝ) :
    ∃! f : ℝ → ℝ, f 0 = x₀ ∧ ∀ t, HasDerivAt f (g (f t)) t := by
  choose f hf0 hf using bounded_lipschitz_interval_solution hlip hbound x₀
  let R : ℝ → ℝ≥0 := fun t => ⟨|t|+1, by positivity⟩
  let φ : ℝ → ℝ := fun t => f (R t) t
  have hφ0 : φ 0 = x₀ := hf0 (R 0)
  have hφ : ∀ t, HasDerivAt φ (g (φ t)) t := by
    intro t
    let B : ℝ≥0 := ⟨|t|+2, by positivity⟩
    have hB : 0 < (B : ℝ) := by change 0 < |t|+2; positivity
    have htB : |t| < (B : ℝ) := by change |t| < |t|+2; linarith
    have heq : φ =ᶠ[𝓝 t] f B := by
      have hev : ∀ᶠ r in 𝓝 t, |r| < (B : ℝ) :=
        (continuous_abs.tendsto t).eventually (eventually_lt_nhds htB)
      filter_upwards [hev] with r hr
      exact scalar_interval_solutions_agree hlip
        (by change 0 < |r|+1; positivity) hB (hf (R r)) (hf B)
        ((hf0 _).trans (hf0 _).symm) (by change |r| < |r|+1; linarith) hr
    have hd := (hf B t (abs_lt.mp htB)).congr_of_eventuallyEq heq
    simpa only [heq.eq_of_nhds] using hd
  refine ⟨φ, ⟨hφ0, hφ⟩, ?_⟩
  intro h hh
  exact ODE_solution_unique_univ (v := fun _ => g) (s := fun _ => univ)
    (fun _ => hlip.lipschitzOnWith) (fun t => ⟨hh.2 t, mem_univ _⟩)
    (fun t => ⟨hφ t, mem_univ _⟩) (hh.1.trans hφ0.symm)

/-- The scalar tangential correction in logarithmic time. -/
def parameterField (q : ℝ → State) (s : ℝ) : ℝ :=
  -(q s 0 * q s 2 + q s 1 * q s 3)

lemma parameterField_eq (q : ℝ → State) (s : ℝ) :
    parameterField q s = -inner ℝ (position (q s)) (tangent (q s)) := by
  simp [parameterField, position, tangent, planePair,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

def parameterFieldDerivative (q : ℝ → State) (s : ℝ) : ℝ :=
  -(q s 2 ^ 2 + q s 3 ^ 2 - q s 4 * q s 0 * q s 3 + q s 4 * q s 1 * q s 2)

lemma parameterField_hasDerivAt {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) (s : ℝ) :
    HasDerivAt (parameterField q) (parameterFieldDerivative q s) s := by
  have hd := hasDerivAt_pi.mp (hq s)
  have hh := (((hd 0).mul (hd 2)).add ((hd 1).mul (hd 3))).neg
  convert! hh using 1
  dsimp [parameterFieldDerivative, field]
  ring

lemma periodic_continuous_norm_bound {f : ℝ → ℝ} {P : ℝ}
    (hp : Function.Periodic f P) (hP : P ≠ 0) (hf : Continuous f) :
    ∃ M : ℝ≥0, ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := (hp.isBounded_of_continuous hP hf).exists_pos_norm_le
  exact ⟨⟨M, hM.le⟩, fun x => hb (f x) (mem_range_self x)⟩

theorem parameterField_bounded_lipschitz {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) :
    ∃ K M : ℝ≥0, LipschitzWith K (parameterField q) ∧
      ∀ x, ‖parameterField q x‖ ≤ M := by
  have hc : Continuous q := continuous_iff_continuousAt.mpr fun s => (hq s).continuousAt
  have hcp : Continuous (parameterField q) := by unfold parameterField; fun_prop
  have hcd : Continuous (parameterFieldDerivative q) := by unfold parameterFieldDerivative; fun_prop
  have hpp : Function.Periodic (parameterField q) P := by
    intro s
    simp only [parameterField, hp s]
  have hpd : Function.Periodic (parameterFieldDerivative q) P := by
    intro s
    simp only [parameterFieldDerivative, hp s]
  obtain ⟨M, hM⟩ := periodic_continuous_norm_bound hpp hP hcp
  obtain ⟨K, hK⟩ := periodic_continuous_norm_bound hpd hP hcd
  refine ⟨K, M, ?_, hM⟩
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun s => (parameterField_hasDerivAt hq s).differentiableAt)
  intro s
  rw [(parameterField_hasDerivAt hq s).deriv]
  exact_mod_cast hK s

/-- The actual tangential correction field of a periodic ODE orbit has a
global parameter flow through every initial parameter. -/
theorem exists_unique_profile_parameter_flow {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (s₀ : ℝ) :
    ∃! ψ : ℝ → ℝ, ψ 0 = s₀ ∧
      ∀ τ, HasDerivAt ψ (-inner ℝ (position (q (ψ τ))) (tangent (q (ψ τ)))) τ := by
  obtain ⟨K, M, hK, hM⟩ := parameterField_bounded_lipschitz hq hp hP
  simpa only [parameterField_eq] using exists_unique_global_scalar_flow hK hM s₀

def logarithmicTime (t : ℝ) : ℝ := Real.log (1+4*t) / 4

lemma logarithmicTime_zero : logarithmicTime 0 = 0 := by simp [logarithmicTime]

lemma expanderRadius_fourth {t : ℝ} (ht : 0 ≤ t) :
    expanderRadius t ^ 4 = 1+4*t := by
  rw [expanderRadius, ← Real.rpow_mul_natCast (by linarith : 0 ≤ 1+4*t)]
  norm_num

lemma logarithmicTime_derivative {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt logarithmicTime (1 / expanderRadius t ^ 4) t := by
  have hx : 0 < 1+4*t := by linarith
  have hd : HasDerivAt (fun s : ℝ => 1+4*s) 4 t := by
    convert! ((hasDerivAt_id t).const_mul 4).const_add 1 using 1
    ring
  have hh := (hd.log hx.ne').div_const 4
  convert! hh using 1
  rw [expanderRadius_fourth ht]
  ring

/-- Differentiating along a genuine parameter solution cancels the entire
tangential velocity of the expanding profile. -/
theorem reparametrized_trajectory_derivative {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1) {ψ : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hψ : HasDerivAt ψ (parameterField q (ψ t) / expanderRadius t ^ 4) t) :
    HasDerivAt (fun r => expandingCurve q r (ψ r))
      ((-scaledForce q (expanderRadius t) (expanderRadius t * ψ t)) • normal (q (ψ t))) t := by
  have hp := (position_derivative (hq (ψ t))).scomp t hψ
  have hd := (expanderRadius_derivative ht).smul hp
  have hR := (expanderRadius_pos ht).ne'
  have hc := expandingCurve_vector_FEF_mod_tangent hq hu ht (ψ t)
  dsimp only at hc
  rw [(expandingCurve_time_derivative q ht (ψ t)).deriv, real_inner_smul_left] at hc
  have halg : expanderRadius t * (parameterField q (ψ t) / expanderRadius t ^ 4) =
      -(1 / expanderRadius t ^ 3 * inner ℝ (position (q (ψ t))) (tangent (q (ψ t)))) := by
    rw [parameterField_eq]
    field_simp
  have hv : (1 / expanderRadius t ^ 3) • position (q (ψ t)) +
      expanderRadius t • ((parameterField q (ψ t) / expanderRadius t ^ 4) • tangent (q (ψ t))) =
      (-scaledForce q (expanderRadius t) (expanderRadius t * ψ t)) • normal (q (ψ t)) := by
    rw [smul_smul, halg, neg_smul, ← sub_eq_add_neg]
    exact hc
  convert! hd using 1
  simpa only [Function.comp_apply, add_comm] using hv.symm

/-- For every initial parameter, an actual parameter solution exists for all
physical times t>=0 and makes the moving point satisfy vector free elastic
flow. Dependence on the initial parameter is not asserted here. -/
theorem exists_reparametrized_trajectory {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (s₀ : ℝ) :
    ∃ ψ : ℝ → ℝ, ψ 0 = s₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt ψ (parameterField q (ψ t) / expanderRadius t ^ 4) t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (fun r => expandingCurve q r (ψ r))
        ((-scaledForce q (expanderRadius t) (expanderRadius t * ψ t)) • normal (q (ψ t))) t) := by
  obtain ⟨K, M, hK, hM⟩ := parameterField_bounded_lipschitz hq hp hP
  obtain ⟨φ, hφ, _⟩ := exists_unique_global_scalar_flow hK hM s₀
  let ψ : ℝ → ℝ := fun t => φ (logarithmicTime t)
  have hψ : ∀ t, 0 ≤ t → HasDerivAt ψ (parameterField q (ψ t) / expanderRadius t ^ 4) t := by
    intro t ht
    have hh := (hφ.2 (logarithmicTime t)).comp t (logarithmicTime_derivative ht)
    convert! hh using 1
    simp [ψ, div_eq_mul_inv]
  refine ⟨ψ, ?_, hψ, fun t ht => reparametrized_trajectory_derivative hq hu ht (hψ t ht)⟩
  simpa [ψ, logarithmicTime_zero] using hφ.1

end
end CentroidEscape

#print axioms CentroidEscape.exists_unique_global_scalar_flow
#print axioms CentroidEscape.exists_reparametrized_trajectory

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Centroid reparametrization audit passed for {checked} declarations."
