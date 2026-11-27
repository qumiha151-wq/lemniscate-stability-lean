import LengthGrowth.ActualFlow.TangentPhysicalIncrement

namespace LengthGrowth.ActualFlow.ForwardImmersion
noncomputable section
open Set Filter
open scoped Topology
variable (c : ForwardImmersion)

/-- The supremum is over all nonnegative physical times, using normalized
arclength on each time slice. -/
def quarticSupRatio (h : ℝ) : ℝ :=
  ⨆ t : Set.Ici (0:ℝ), c.tangentQuartic t.property h / h

private theorem quartic_ratio_bdd {h : ℝ} (hp : 0<h) :
    BddAbove (range (fun t : Set.Ici (0:ℝ) => c.tangentQuartic t.property h / h)) := by
  refine ⟨16/h,?_⟩
  rintro _ ⟨t,rfl⟩
  exact div_le_div_of_nonneg_right (c.tangent_quartic_bounds t.property h).2.2 hp.le

theorem quartic_ratio_le_sup {t h : ℝ} (ht : 0≤t) (hp : 0<h) :
    c.tangentQuartic ht h/h ≤ c.quarticSupRatio h :=
  le_ciSup (c.quartic_ratio_bdd hp) (⟨t,ht⟩ : Set.Ici (0:ℝ))

private theorem quartic_sup_nonnegative {h : ℝ} (hp : 0<h) : 0≤c.quarticSupRatio h :=
  (div_nonneg (c.tangent_quartic_bounds (t:=0) le_rfl h).1 hp.le).trans
    (c.quartic_ratio_le_sup le_rfl hp)

/-- A geometric two-point quantity characterizes fourth-root length growth
of a single actual free elastic flow, uniformly over its entire lifetime. -/
theorem quarter_length_iff_vanishing_tangent_increments (hf : c.IsNormalFEF) :
    c.HasQuarterLengthBound ↔ Tendsto c.quarticSupRatio (𝓝[>] (0:ℝ)) (𝓝 0) := by
  constructor
  · intro growth
    obtain ⟨K,bound⟩ := (c.quarter_length_iff_bounded_energyLength hf).mp growth
    have kn : 0≤K := (mul_nonneg (c.energy_nonneg 0) (c.length_nonneg 0)).trans (bound 0 le_rfl)
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro ε ep
    have kp : 0<8*K+1 := by linarith
    refine ⟨ε/(8*K+1),div_pos ep kp,?_⟩
    intro h hh hd
    have hp : 0<h := hh
    have small : h<ε/(8*K+1) := by simpa [Real.dist_eq,abs_of_pos hp] using hd
    have pos := (lt_div_iff₀ kp).mp small
    have us : c.quarticSupRatio h≤8*h*K := by
      apply ciSup_le
      intro t
      apply (div_le_iff₀ hp).mpr
      have ut : c.normalizedProduct t≤K := bound t t.property
      have cap := (c.tangent_quartic_bounds t.property h).2.1
      have w := mul_le_mul_of_nonneg_left ut (show 0≤8*h^2 by positivity)
      nlinarith only [cap,w]
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (c.quartic_sup_nonnegative hp)]
    linarith
  · intro vanish
    by_contra fail
    obtain ⟨δ,dp,bound⟩ := Metric.tendsto_nhdsWithin_nhds.mp vanish (1/4194304) (by norm_num)
    obtain ⟨t,ht,_,_,_,h,hp,small,spike⟩ := c.small_lags_at_high_records hf fail dp 0 0
    have e := bound (x:=h) (show h∈Ioi (0:ℝ) from hp) (by simpa [Real.dist_eq,abs_of_pos hp] using small)
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (c.quartic_sup_nonnegative hp)] at e
    have lower : 1/4194304≤c.tangentQuartic ht.le h/h := (le_div_iff₀ hp).mpr (by linarith)
    exact (not_le_of_gt e) (lower.trans (c.quartic_ratio_le_sup ht.le hp))

end
end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_iff_vanishing_tangent_increments
