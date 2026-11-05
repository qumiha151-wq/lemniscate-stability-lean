import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Integrating an exponentially decaying real angular velocity selects
one limiting rotation. The angle is the actual integral of the velocity. -/

noncomputable section
namespace Lemniscate
open Set MeasureTheory Filter
open scoped Topology

private theorem decaying_exponential_tail (ν : ℝ) (hν : 0 < ν) (a : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-ν*t)) (Ioi a) ∧
      (∫ t in Ioi a, Real.exp (-ν*t)) = Real.exp (-ν*a)/ν := by
  have hνne : ν ≠ 0 := ne_of_gt hν
  have hd (t : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-ν*y)/(-ν))
      (Real.exp (-ν*t)) t := by
    convert! (((hasDerivAt_id t).const_mul (-ν)).exp.div_const (-ν)) using 1
    field_simp [hνne,id_eq]
    <;> rfl
  have hi (c d : ℝ) : IntervalIntegrable (fun t : ℝ => Real.exp (-ν*t)) volume c d :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable c d
  have heval (c d : ℝ) : (∫ t in c..d, Real.exp (-ν*t)) =
      (Real.exp (-ν*c)-Real.exp (-ν*d))/ν := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hi c d)]
    field_simp [hνne]
    <;> ring
  have hI : IntegrableOn (fun t : ℝ => Real.exp (-ν*t)) (Ioi a) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (Real.exp (-ν*a)/ν) a
      (fun d => (hi a d).1) tendsto_id
    apply Eventually.of_forall
    intro d
    simp_rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    rw [heval]
    exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hν.le
  have hm : Tendsto (fun t : ℝ => (-ν)*t) atTop atBot :=
    tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hν) tendsto_id
  have he : Tendsto (fun t : ℝ => Real.exp (-ν*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hm
  have hv := intervalIntegral_tendsto_integral_Ioi a hI tendsto_id
  simp_rw [heval] at hv
  have hl : Tendsto (fun t : ℝ => (Real.exp (-ν*a)-Real.exp (-ν*t))/ν)
      atTop (𝓝 (Real.exp (-ν*a)/ν)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub he).div_const ν
  exact ⟨hI,tendsto_nhds_unique hv hl⟩

/-- A locally integrable real angular velocity, continuous at positive
times and with an exponential tail, has a continuous primitive converging
to one real angle with the corresponding quantitative tail estimate. -/
private theorem rotation_angle_convergence_data
    (ω : ℝ → ℝ) (hlocal : ∀ a b : ℝ, IntervalIntegrable ω volume a b)
    (hcont : ContinuousOn ω (Ioi (0:ℝ)))
    (t₀ ν B : ℝ) (ht₀ : 0 < t₀) (hν : 0 < ν) (hB : 0 ≤ B)
    (hbound : ∀ t : ℝ, t₀ ≤ t → |ω t| ≤ B*Real.exp (-ν*t)) :
    ∃ θ : ℝ → ℝ, ∃ θlim : ℝ,
      (∀ t, θ t = ∫ s in (0:ℝ)..t, ω s) ∧ Continuous θ ∧ θ 0 = 0 ∧
      (∀ t : ℝ, 0 < t → HasDerivAt θ (ω t) t) ∧
      (∀ t : ℝ, t₀ ≤ t → |θlim-θ t| ≤ (B/ν)*Real.exp (-ν*t)) ∧
      Tendsto θ atTop (𝓝 θlim) := by
  let θ : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, ω s
  have htailInt : IntegrableOn ω (Ioi t₀) := by
    have hc : ContinuousOn ω (Ioi t₀) := hcont.mono
      (fun t ht => lt_trans ht₀ ht)
    apply (((decaying_exponential_tail ν hν t₀).1).const_mul B).mono'
      (hc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs] using hbound t ht.le
  let θlim := θ t₀+∫ s in Ioi t₀, ω s
  have htail (t : ℝ) (ht : t₀ ≤ t) :
      θlim-θ t = ∫ s in Ioi t, ω s := by
    have hsplit := intervalIntegral.integral_interval_add_Ioi htailInt
      (htailInt.mono_set (Ioi_subset_Ioi ht))
    have hfinite := intervalIntegral.integral_add_adjacent_intervals
      (hlocal 0 t₀) (hlocal t₀ t)
    dsimp only [θlim,θ]
    linarith only [hsplit,hfinite]
  have hestimate (t : ℝ) (ht : t₀ ≤ t) :
      |θlim-θ t| ≤ (B/ν)*Real.exp (-ν*t) := by
    rw [htail t ht,← Real.norm_eq_abs]
    have hbInt : IntegrableOn (fun s : ℝ => B*Real.exp ((-ν)*s)) (Ioi t) :=
      ((decaying_exponential_tail ν hν t).1).const_mul B
    calc
      ‖∫ s in Ioi t, ω s‖ ≤ ∫ s in Ioi t, B*Real.exp ((-ν)*s) := by
        apply norm_integral_le_of_norm_le hbInt
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        simpa only [Real.norm_eq_abs] using hbound s (ht.trans hs.le)
      _ = (B/ν)*Real.exp (-ν*t) := by
        rw [integral_const_mul,(decaying_exponential_tail ν hν t).2]
        field_simp [ne_of_gt hν]
        <;> ring
  have hlim : Tendsto (fun t : ℝ => (B/ν)*Real.exp (-ν*t)) atTop (𝓝 0) := by
    have hm : Tendsto (fun t : ℝ => (-ν)*t) atTop atBot :=
      tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hν) tendsto_id
    simpa only [mul_zero,Function.comp_def] using!
      (Real.tendsto_exp_atBot.comp hm).const_mul (B/ν)
  refine ⟨θ,θlim,fun _ => rfl,intervalIntegral.continuous_primitive hlocal 0,?_,?_,hestimate,?_⟩
  · exact intervalIntegral.integral_same
  · intro t ht
    exact intervalIntegral.integral_hasDerivAt_right (hlocal 0 t)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hcont t ht)
      (hcont.continuousAt (isOpen_Ioi.mem_nhds ht))
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hb : ∀ᶠ t : ℝ in atTop, (B/ν)*Real.exp (-ν*t) < ε :=
      hlim.eventually (gt_mem_nhds hε)
    obtain ⟨a,ha⟩ := eventually_atTop.mp hb
    refine ⟨max a t₀,fun t ht => ?_⟩
    have ht₀ := (le_max_right a t₀).trans ht
    have hta := (le_max_left a t₀).trans ht
    rw [Real.dist_eq,abs_sub_comm]
    exact (hestimate t ht₀).trans_lt (ha t hta)

/-- One actual rotation angle and one limiting angle work for every
subsequent exponential tail estimate of the same angular velocity. -/
theorem rotation_angle_convergence
    (ω : ℝ → ℝ) (hlocal : ∀ a b : ℝ, IntervalIntegrable ω volume a b)
    (hcont : ContinuousOn ω (Ioi (0:ℝ)))
    (t₀ ν B : ℝ) (ht₀ : 0<t₀) (hν : 0<ν) (hB : 0≤B)
    (hbound : ∀ t : ℝ, t₀≤t → |ω t|≤B*Real.exp (-ν*t)) :
    ∃ θ : ℝ → ℝ, ∃ θlim : ℝ,
      (∀ t, θ t=∫ s in (0:ℝ)..t, ω s) ∧ Continuous θ ∧ θ 0=0 ∧
      (∀ t : ℝ, 0<t → HasDerivAt θ (ω t) t) ∧
      Tendsto θ atTop (𝓝 θlim) ∧
      ∀ t₁ ν₁ B₁ : ℝ, 0<t₁ → 0<ν₁ → 0≤B₁ →
        (∀ t : ℝ, t₁≤t → |ω t|≤B₁*Real.exp (-ν₁*t)) →
        ∀ t : ℝ, t₁≤t → |θlim-θ t|≤(B₁/ν₁)*Real.exp (-ν₁*t) := by
  obtain ⟨θ,θlim,hformula,hc,hzero,hd,_,hlim⟩ :=
    rotation_angle_convergence_data ω hlocal hcont t₀ ν B ht₀ hν hB hbound
  refine ⟨θ,θlim,hformula,hc,hzero,hd,hlim,?_⟩
  intro t₁ ν₁ B₁ ht₁ hν₁ hB₁ hbound₁
  obtain ⟨θ₁,θlim₁,hformula₁,_,_,_,htail₁,hlim₁⟩ :=
    rotation_angle_convergence_data ω hlocal hcont t₁ ν₁ B₁ ht₁ hν₁ hB₁ hbound₁
  have heq : θ₁=θ := funext fun t => (hformula₁ t).trans (hformula t).symm
  have hsame : θlim₁=θlim := tendsto_nhds_unique (heq ▸ hlim₁) hlim
  intro t ht
  simpa only [heq,hsame] using htail₁ t ht

end Lemniscate
