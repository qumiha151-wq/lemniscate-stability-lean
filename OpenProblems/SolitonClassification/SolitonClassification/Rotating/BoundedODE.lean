import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Lean.Util.CollectAxioms

/-! Independent bounded-field existence infrastructure for rotating support ODEs.
This is not yet a global existence proof for the original polynomial support field.
No other open-problem project is imported. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
set_option backward.isDefEq.respectTransparency false
theorem bounded_lipschitz_interval_solution {g : E → E} {K M : ℝ≥0}
    (hlip : LipschitzWith K g) (hbound : ∀ x, ‖g x‖ ≤ M)
    (x₀ : E) (T : ℝ≥0) :
    ∃ f : ℝ → E, f 0 = x₀ ∧
      ∀ t ∈ Ioo (-(T : ℝ)) (T : ℝ), HasDerivAt f (g (f t)) t := by
  let t₀ : Icc (-(T : ℝ)) (T : ℝ) := ⟨0, by simp⟩
  have hp : IsPicardLindelof (fun _ => g) t₀ x₀ (M*T) 0 M K := by
    refine ⟨fun _ _ => hlip.lipschitzOnWith, fun _ _ => continuousOn_const,
      fun _ _ x _ => hbound x, ?_⟩
    simp [t₀]
  obtain ⟨f, h0, hf⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨f, h0, fun t ht => ?_⟩
  exact (hf t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

omit [CompleteSpace E] in
lemma interval_solutions_agree {g : E → E} {K : ℝ≥0}
    (hlip : LipschitzWith K g) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {f h : ℝ → E}
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

/-- A Banach-space bounded globally Lipschitz vector field admits a unique global
solution through each initial point. -/
theorem exists_unique_global_bounded_flow {g : E → E} {K M : ℝ≥0}
    (hlip : LipschitzWith K g) (hbound : ∀ x, ‖g x‖ ≤ M) (x₀ : E) :
    ∃! f : ℝ → E, f 0 = x₀ ∧ ∀ t, HasDerivAt f (g (f t)) t := by
  choose f hf0 hf using bounded_lipschitz_interval_solution hlip hbound x₀
  let R : ℝ → ℝ≥0 := fun t => ⟨|t|+1, by positivity⟩
  let φ : ℝ → E := fun t => f (R t) t
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
      exact interval_solutions_agree hlip
        (by change 0 < |r|+1; positivity) hB (hf (R r)) (hf B)
        ((hf0 _).trans (hf0 _).symm) (by change |r| < |r|+1; linarith) hr
    have hd := (hf B t (abs_lt.mp htB)).congr_of_eventuallyEq heq
    simpa only [heq.eq_of_nhds] using hd
  refine ⟨φ, ⟨hφ0, hφ⟩, ?_⟩
  intro h hh
  exact ODE_solution_unique_univ (v := fun _ => g) (s := fun _ => univ)
    (fun _ => hlip.lipschitzOnWith) (fun t => ⟨hh.2 t, mem_univ _⟩)
    (fun t => ⟨hφ t, mem_univ _⟩) (hh.1.trans hφ0.symm)

end
end SolitonClassification.Rotating
#print axioms SolitonClassification.Rotating.exists_unique_global_bounded_flow

