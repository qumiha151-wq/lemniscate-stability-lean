import LengthGrowth.ScalarDissipation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Lean.Util.CollectAxioms

/-! A sharper scalar consequence of the restart dissipation estimate.
The energy reservoir need only be bounded below; no zero energy limit is
assumed. Geometric PDE identities remain outside this scalar module. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FreeElasticScalar

theorem restart_sublinear_square_envelope {L H : ℝ → ℝ}
    (hH : ∀ s, 0 ≤ s → 0 ≤ H s)
    (hr : ∀ s t, 0 ≤ s → s ≤ t →
      (L t-L s)^2 ≤ (t-s)*(H s-H t))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t, S ≤ t →
      (L t)^2 ≤ 2*t*δ + 2*(L S)^2 := by
  let A : Set ℝ := H '' Ici 0
  have hA : A.Nonempty := ⟨H 0, ⟨0, mem_Ici.mpr le_rfl, rfl⟩⟩
  have hb : BddBelow A := by
    refine ⟨0, ?_⟩
    rintro a ⟨s, hs, rfl⟩
    exact hH s hs
  obtain ⟨a, ha, hnear⟩ := exists_lt_of_csInf_lt hA
    (show sInf A < sInf A+δ by linarith)
  obtain ⟨S,hS,rfl⟩ := ha
  refine ⟨S,hS,?_⟩
  intro t hSt
  have ht : 0 ≤ t := hS.trans hSt
  have hlow : sInf A ≤ H t := csInf_le hb ⟨t,ht,rfl⟩
  have hdrop : H S-H t ≤ δ := by linarith
  have hq := (hr S t hS hSt).trans
    (mul_le_mul_of_nonneg_left hdrop (sub_nonneg.mpr hSt))
  nlinarith [sq_nonneg (L t-2*L S),mul_nonneg hS hδ.le]

theorem restart_square_div_time_tendsto_zero {L H : ℝ → ℝ}
    (hH : ∀ s, 0 ≤ s → 0 ≤ H s)
    (hr : ∀ s t, 0 ≤ s → s ≤ t →
      (L t-L s)^2 ≤ (t-s)*(H s-H t)) :
    Tendsto (fun t => (L t)^2/t) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨S,hS,henv⟩ := restart_sublinear_square_envelope hH hr
    (show 0<ε/4 by positivity)
  filter_upwards [eventually_ge_atTop (max (S+1) (4*(L S)^2/ε+1))] with t ht
  have hSt : S ≤ t := by have := (le_max_left (S+1) (4*(L S)^2/ε+1)).trans ht; linarith
  have htpos : 0<t := by have := (le_max_left (S+1) (4*(L S)^2/ε+1)).trans ht; linarith
  have hlarge : 4*(L S)^2/ε < t := by
    have := (le_max_right (S+1) (4*(L S)^2/ε+1)).trans ht
    linarith
  have hconst : 4*(L S)^2 < t*ε := (div_lt_iff₀ hε).mp hlarge
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (sq_nonneg _) htpos.le)]
  apply (div_lt_iff₀ htpos).mpr
  nlinarith [henv t hSt]

/-- The restart estimate implies `L(t)=o(sqrt(t))` even when H has an
unknown positive limiting value. No sign assumption on L is needed. -/
theorem restart_length_div_sqrt_tendsto_zero {L H : ℝ → ℝ}
    (hH : ∀ s, 0 ≤ s → 0 ≤ H s)
    (hr : ∀ s t, 0 ≤ s → s ≤ t →
      (L t-L s)^2 ≤ (t-s)*(H s-H t)) :
    Tendsto (fun t => L t/Real.sqrt t) atTop (𝓝 0) := by
  have hs := (Real.continuous_sqrt.tendsto 0).comp
    (restart_square_div_time_tendsto_zero hH hr)
  have habs : Tendsto (fun t => |L t/Real.sqrt t|) atTop (𝓝 0) := by
    convert hs using 1
    · funext t
      simp only [Function.comp_def]
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    · simp only [Real.sqrt_zero]
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

end FreeElasticScalar

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`FreeElasticScalar).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Subsqrt growth audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Subsqrt growth audit passed for {count} declarations; standard axioms only."
