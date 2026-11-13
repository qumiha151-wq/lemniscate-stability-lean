import LengthGrowth.EnergyDecay

/-! Conditional weighted length comparison on forward time. The scalar
energy envelope is an explicit premise here, to be derived from actual
fifth-power coercivity in the geometric wrapper. No monotone length or
scale-invariant product bound is assumed. -/

noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace FreeElasticScalar

theorem length_rate_young (E D ell a : ℝ) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (ha : 0 < a) (hq : ell ^ 2 ≤ 2 * E * D) :
    ell ≤ a * D + E / (2 * a) := by
  have hnon : 0 ≤ a * D + E / (2 * a) := by positivity
  have hid : (a * D + E / (2 * a)) ^ 2 =
      2 * E * D + (a * D - E / (2 * a)) ^ 2 := by
    field_simp [ne_of_gt ha]
    ring
  apply le_of_sq_le_sq _ hnon
  rw [hid]
  nlinarith [sq_nonneg (a * D - E / (2 * a))]

theorem fourthRoot_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt fourthRoot (1 / (4 * fourthRoot x ^ 3)) x := by
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hx)).sqrt
    (ne_of_gt (Real.sqrt_pos.mpr hx))
  convert! h using 1
  change 1 / (4 * fourthRoot x ^ 3) =
    (1 / (2 * Real.sqrt x)) / (2 * fourthRoot x)
  rw [← fourthRoot_sq x]
  field_simp [ne_of_gt (fourthRoot_pos hx)]
  ring

theorem weighted_length_shifted_bound (L E ell D : ℝ → ℝ) (B τ : ℝ)
    (hτ : 0 < τ) (hLc : ContinuousOn L (Ici 0)) (hEc : ContinuousOn E (Ici 0))
    (hEn : ∀ s, 0 ≤ s → 0 ≤ E s) (hDn : ∀ s, 0 < s → 0 ≤ D s)
    (hLd : ∀ s, 0 < s → HasDerivAt L (ell s) s)
    (hEd : ∀ s, 0 < s → HasDerivAt E (-D s) s)
    (hquad : ∀ s, 0 < s → ell s ^ 2 ≤ 2 * E s * D s)
    (henv : ∀ s, 0 ≤ s → E s ≤ B / fourthRoot (s + τ))
    (t : ℝ) (ht : 0 ≤ t) :
    L t + Real.sqrt (t + τ) * E t ≤
      L 0 + Real.sqrt τ * E 0 + 4 * B * (fourthRoot (t + τ) - fourthRoot τ) := by
  let J : ℝ → ℝ := fun s =>
    L s + Real.sqrt (s + τ) * E s - 4 * B * fourthRoot (s + τ)
  have hsc : Continuous (fun s : ℝ => Real.sqrt (s + τ)) :=
    (continuous_id.add continuous_const).sqrt
  have hqc : Continuous (fun s : ℝ => fourthRoot (s + τ)) :=
    fourthRoot_continuous.comp (continuous_id.add continuous_const)
  have hJc : ContinuousOn J (Icc 0 t) :=
    ((hLc.add (hsc.continuousOn.mul hEc)).sub
      (continuousOn_const.mul hqc.continuousOn)).mono (fun _ hs => hs.1)
  have hJd (s : ℝ) (hs : s ∈ Ioo 0 t) : HasDerivAt J
      (ell s + E s / (2 * Real.sqrt (s + τ)) - Real.sqrt (s + τ) * D s -
        B / fourthRoot (s + τ) ^ 3) s := by
    have hpos : 0 < s + τ := by linarith [hs.1]
    have hsd := ((hasDerivAt_id s).add_const τ).sqrt (ne_of_gt hpos)
    have hqd := (fourthRoot_hasDerivAt hpos).comp s ((hasDerivAt_id s).add_const τ)
    simp only [id_eq, mul_one] at hsd hqd
    convert! ((hLd s hs.1).add (hsd.mul (hEd s hs.1))).sub (hqd.const_mul (4 * B)) using 1
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hpos), ne_of_gt (fourthRoot_pos hpos)]
    ring
  have hanti : AntitoneOn J (Icc 0 t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t) hJc
      (f' := fun s => ell s + E s / (2 * Real.sqrt (s + τ)) -
        Real.sqrt (s + τ) * D s - B / fourthRoot (s + τ) ^ 3)
    · intro s hs
      exact (hJd s (by simpa only [interior_Icc] using hs)).hasDerivWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 t := by simpa only [interior_Icc] using hs
      have hpos : 0 < s + τ := by linarith [hs'.1]
      have ha := Real.sqrt_pos.mpr hpos
      have hq := fourthRoot_pos hpos
      have hy := length_rate_young (E s) (D s) (ell s) (Real.sqrt (s + τ))
        (hEn s hs'.1.le) (hDn s hs'.1) ha (hquad s hs'.1)
      have he : E s / Real.sqrt (s + τ) ≤ B / fourthRoot (s + τ) ^ 3 := by
        have h := div_le_div_of_nonneg_right (henv s hs'.1.le) ha.le
        have hid : (B / fourthRoot (s + τ)) / Real.sqrt (s + τ) =
            B / fourthRoot (s + τ) ^ 3 := by
          rw [← fourthRoot_sq (s + τ)]
          field_simp [ne_of_gt hq]
        simpa only [hid] using h
      have hhalf : E s / (2 * Real.sqrt (s + τ)) +
          E s / (2 * Real.sqrt (s + τ)) = E s / Real.sqrt (s + τ) := by ring
      linarith
  have h := hanti (show 0 ∈ Icc 0 t from ⟨le_rfl, ht⟩)
    (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩) ht
  dsimp only [J] at h
  simp only [zero_add] at h
  linarith

/-- A parameter limit of positive shifts; no time derivative at zero is
used. The nonnegative weighted energy term is retained in the conclusion. -/
theorem weighted_length_zero_shift (L E ell D : ℝ → ℝ) (B τ : ℝ)
    (hB : 0 ≤ B) (hτ : 0 < τ)
    (hLc : ContinuousOn L (Ici 0)) (hEc : ContinuousOn E (Ici 0))
    (hEn : ∀ s, 0 ≤ s → 0 ≤ E s) (hDn : ∀ s, 0 < s → 0 ≤ D s)
    (hLd : ∀ s, 0 < s → HasDerivAt L (ell s) s)
    (hEd : ∀ s, 0 < s → HasDerivAt E (-D s) s)
    (hquad : ∀ s, 0 < s → ell s ^ 2 ≤ 2 * E s * D s)
    (henv : ∀ s, 0 ≤ s → E s ≤ B / fourthRoot (s + τ))
    (t : ℝ) (ht : 0 ≤ t) :
    L t + Real.sqrt t * E t ≤ L 0 + 4 * B * fourthRoot t := by
  have hδ (δ : ℝ) (hd : 0 < δ) (hdt : δ ≤ τ) :
      L t + Real.sqrt (t + δ) * E t ≤
        L 0 + Real.sqrt δ * E 0 + 4 * B * (fourthRoot (t + δ) - fourthRoot δ) := by
    apply weighted_length_shifted_bound L E ell D B δ hd hLc hEc hEn hDn
      hLd hEd hquad ?_ t ht
    intro s hs
    apply (henv s hs).trans
    exact div_le_div_of_nonneg_left hB (fourthRoot_pos (by linarith))
      (fourthRoot_mono (by linarith : s + δ ≤ s + τ))
  let f : ℝ → ℝ := fun δ => L t + Real.sqrt (t + δ) * E t
  let g : ℝ → ℝ := fun δ =>
    L 0 + Real.sqrt δ * E 0 + 4 * B * (fourthRoot (t + δ) - fourthRoot δ)
  have hf : Continuous f := continuous_const.add
    ((continuous_const.add continuous_id).sqrt.mul continuous_const)
  have hg : Continuous g :=
    (continuous_const.add (Real.continuous_sqrt.mul continuous_const)).add
      (continuous_const.mul ((fourthRoot_continuous.comp
        (continuous_const.add continuous_id)).sub fourthRoot_continuous))
  have he : ∀ᶠ δ in 𝓝[>] (0 : ℝ), f δ ≤ g δ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iic_mem_nhds hτ)] with δ hd hdt
    exact hδ δ hd hdt
  have h := le_of_tendsto_of_tendsto
    ((hf.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds) he
  simpa [f, g, fourthRoot] using h

/-- Fifth-power energy coercivity implies quarter-power length growth via
the actual scalar derivative assumptions. No product bound is assumed. -/
theorem coercive_quarter_length_bound (L E ell D : ℝ → ℝ) (c B : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hcoef : 1 ≤ 4 * c * B ^ 4)
    (hLc : ContinuousOn L (Ici 0)) (hEc : ContinuousOn E (Ici 0))
    (hEp : ∀ s, 0 ≤ s → 0 < E s)
    (hLd : ∀ s, 0 < s → HasDerivAt L (ell s) s)
    (hEd : ∀ s, 0 < s → HasDerivAt E (-D s) s)
    (hquad : ∀ s, 0 < s → ell s ^ 2 ≤ 2 * E s * D s)
    (hcoerc : ∀ s, 0 < s → c * E s ^ 5 ≤ D s)
    (t : ℝ) (ht : 0 ≤ t) :
    L t + Real.sqrt t * E t ≤ L 0 + 4 * B * fourthRoot t := by
  let τ : ℝ := B ^ 4 / E 0 ^ 4
  have hE0 := hEp 0 (by rfl)
  have hτ : 0 < τ := div_pos (pow_pos hB 4) (pow_pos hE0 4)
  have hi : E 0 ^ 4 * τ ≤ B ^ 4 := by
    have heq : E 0 ^ 4 * τ = B ^ 4 := by
      dsimp only [τ]
      field_simp [ne_of_gt hE0]
    exact heq.le
  apply weighted_length_zero_shift L E ell D B τ hB.le hτ hLc hEc
    (fun s hs => (hEp s hs).le)
    (fun s hs => (mul_nonneg hc.le (pow_nonneg (hEp s hs.le).le 5)).trans (hcoerc s hs))
    hLd hEd hquad ?_ t ht
  intro s hs
  exact energy_le_shifted_fourthRoot E D c B τ hB hτ hEc hEp hEd hcoerc hi hcoef s hs

end FreeElasticScalar

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`FreeElasticScalar).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Weighted length audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"CONDITIONAL_WEIGHTED_LENGTH_AUDIT {count}: standard three axioms only."
