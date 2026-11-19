import LengthGrowth.ActualFlow.IntrinsicScaling
import LengthGrowth.ActualFlow.ForwardDissipation

/-! Positive dilations and forward time shifts of a parametrized normal flow. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

/-- A parabolic rescaling of a given forward immersion, starting at time `s`. -/
def rescaled (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) : ForwardImmersion where
  period := c.period
  period_pos := c.period_pos
  position := fun τ => scalePosition r (c.position (s + τ / r ^ 4))
  periodic := fun τ hτ => scalePosition_periodic r (c.periodic _
    (add_nonneg hs (div_nonneg hτ (pow_pos hr 4).le)))
  initial_smooth := by
    simpa only [zero_div, add_zero] using scalePosition_smooth r (c.position_slice_smooth hs)
  interior_joint_smooth := by
    let f := fun z : ℝ × ℝ => (s + z.1 / r ^ 4, z.2)
    have hf : ContDiff ℝ ∞ f := (contDiff_const.add (contDiff_fst.div_const _)).prodMk contDiff_snd
    have hm : MapsTo f (Ioi 0 ×ˢ (univ : Set ℝ)) (Ioi 0 ×ˢ (univ : Set ℝ)) :=
      fun z hz => ⟨add_pos_of_nonneg_of_pos hs (div_pos hz.1 (pow_pos hr 4)), mem_univ _⟩
    exact (c.interior_joint_smooth.comp hf.contDiffOn hm).const_smul r
  immersion := fun τ hτ => scalePosition_regular hr
    (c.immersion _ (add_nonneg hs (div_nonneg hτ (pow_pos hr 4).le)))
  spatial_jets_continuous := by
    intro j hj
    let f := fun z : ℝ × ℝ => (s + z.1 / r ^ 4, z.2)
    have hf : Continuous f := (continuous_const.add (continuous_fst.div_const _)).prodMk continuous_snd
    have hm : MapsTo f (Ici 0 ×ˢ (univ : Set ℝ)) (Ici 0 ×ˢ (univ : Set ℝ)) :=
      fun z hz => ⟨add_nonneg hs (div_nonneg hz.1 (pow_pos hr 4).le), mem_univ _⟩
    simpa only [scalePosition_iteratedDeriv, Pi.smul_def, Function.comp_def, f] using
      (((c.spatial_jets_continuous j hj).comp hf.continuousOn hm).const_smul r)

@[simp] theorem rescaled_period (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) :
    (c.rescaled r s hr hs).period = c.period := rfl

@[simp] theorem rescaled_position (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (τ u : ℝ) :
    (c.rescaled r s hr hs).position τ u = r • c.position (s + τ / r ^ 4) u := rfl

theorem rescaled_isNormalFEF (hflow : c.IsNormalFEF) (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) :
    (c.rescaled r s hr hs).IsNormalFEF := by
  intro τ hτ u
  let H := s + τ / r ^ 4
  have hH : 0 < H := add_pos_of_nonneg_of_pos hs (div_pos hτ (pow_pos hr 4))
  have htime : HasDerivAt (fun a : ℝ => s + a / r ^ 4) (1 / r ^ 4) τ :=
    ((hasDerivAt_id τ).div_const _).const_add s
  have hd := ((hflow H hH u).scomp τ htime).const_smul r
  change HasDerivAt (fun a : ℝ => r • c.position (s + a / r ^ 4) u)
    (-(force (scalePosition r (c.position H)) u : ℂ) * normal (scalePosition r (c.position H)) u) τ
  suffices hh : -(force (scalePosition r (c.position H)) u : ℂ) * normal (scalePosition r (c.position H)) u =
      r • ((1 / r ^ 4 : ℝ) • (-(force (c.position H) u : ℂ) * normal (c.position H) u)) by
    rw [hh]
    simpa only [Pi.smul_def, Function.comp_def] using hd
  rw [scalePosition_force hr, scalePosition_normal hr]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow]
  have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  field_simp [hn]

theorem rescaled_length (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (τ : ℝ) :
    (c.rescaled r s hr hs).length τ = r * c.length (s + τ / r ^ 4) :=
  scalePosition_materialLength hr _ _

theorem rescaled_energy (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (τ : ℝ) :
    (c.rescaled r s hr hs).energy τ = c.energy (s + τ / r ^ 4) / r :=
  scalePosition_materialEnergy hr _ _

theorem rescaled_dissipation (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (τ : ℝ) :
    (c.rescaled r s hr hs).dissipation τ = c.dissipation (s + τ / r ^ 4) / r ^ 5 :=
  scalePosition_materialDissipation hr _ _

theorem rescaled_lengthRate (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (τ : ℝ) :
    (c.rescaled r s hr hs).lengthRate τ = c.lengthRate (s + τ / r ^ 4) / r ^ 3 :=
  scalePosition_materialLengthRate hr _ _

end LengthGrowth.ActualFlow.ForwardImmersion

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf n || (`FreeElasticScalar).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual forward rescaling: {count} declarations; standard axioms only."
