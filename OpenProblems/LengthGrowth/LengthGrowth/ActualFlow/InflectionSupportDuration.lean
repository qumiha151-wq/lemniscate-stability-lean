import LengthGrowth.ActualFlow.ExactInflectionGrowth

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Finite time spent at one band of weak positive outward inflection rates
implies the quarter-power bound, given the tail's four-thirds estimate. -/
theorem quarter_length_of_finite_weak_inflection_duration (flow : c.IsNormalFEF)
    {a δ : ℝ} (ha : 0<a) (hδ : 0<δ)
    (fourThirds : IntegrableOn (fun t => (c.physicalInflectionRate t)^(4/3:ℝ)) (Ioi a))
    (finite : volume {t : ℝ | a<t ∧ 0<c.physicalInflectionRate t ∧
        c.physicalInflectionRate t<δ} < ⊤) : c.HasQuarterLengthBound := by
  classical
  let g := fun t => if a≤t then c.physicalInflectionRate t else 0
  have mg : Measurable g := (c.upperSemicontinuous_physicalInflectionRate_cut ha).measurable
  let weak := Ioi a ∩ g ⁻¹' Ioo 0 δ
  have mweak : MeasurableSet weak := measurableSet_Ioi.inter (mg measurableSet_Ioo)
  have eq : weak = {t : ℝ | a<t ∧ 0<c.physicalInflectionRate t ∧ c.physicalInflectionRate t<δ} := by
    ext t
    by_cases h : a<t
    · simp [weak,g,h,h.le]
    · simp [weak,h]
  have weakBound : IntegrableOn (weak.indicator (fun _ => δ)) (Ioi a) :=
    ((integrableOn_const ((eq ▸ finite).ne) : IntegrableOn (fun _ : ℝ => δ) weak).integrable_indicator mweak).integrableOn
  have ms : AEStronglyMeasurable c.physicalInflectionRate (volume.restrict (Ioi a)) :=
    mg.aestronglyMeasurable.congr (by
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
      change a<t at ht
      simp [g,ht.le])
  apply c.quarter_length_of_integrable_physical_inflection_rate flow ha
  apply (weakBound.add (fourThirds.const_mul (δ^(1/3:ℝ))⁻¹)).mono' ms
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
  let P := c.physicalInflectionRate t
  have hp : 0≤P := c.physicalInflectionRate_nonneg (ha.trans ht)
  have dp := Real.rpow_pos_of_pos hδ (1/3:ℝ)
  change ‖P‖ ≤ weak.indicator (fun _ => δ) t+(δ^(1/3:ℝ))⁻¹*P^(4/3:ℝ)
  rw [Real.norm_of_nonneg hp]
  by_cases w : t∈weak
  · rw [indicator_of_mem w]
    have small : P<δ := ((eq ▸ w).2).2
    exact small.le.trans (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr dp.le) (Real.rpow_nonneg hp _)))
  · rw [indicator_of_notMem w,zero_add]
    by_cases zero : P=0
    · exact zero ▸ mul_nonneg (inv_nonneg.mpr dp.le) (Real.rpow_nonneg (by norm_num) _)
    have big : δ≤P := le_of_not_gt (fun small => w (eq.symm ▸ ⟨ht,lt_of_le_of_ne hp (Ne.symm zero),small⟩))
    have cmp := Real.rpow_le_rpow hδ.le big (by norm_num : (0:ℝ)≤1/3)
    rw [←div_eq_inv_mul]
    apply (le_div_iff₀ dp).mpr
    calc
      P*δ^(1/3:ℝ) ≤ P*P^(1/3:ℝ) := mul_le_mul_of_nonneg_left cmp hp
      _ = P^(4/3:ℝ) := by rw [mul_comm,←Real.rpow_add_one zero]; norm_num

/-- Failure of the quarter-power bound forces infinite time in every open
band (0,δ) on each tail with a four-thirds estimate. -/
theorem weak_inflection_duration_eq_top_of_no_quarter_length (flow : c.IsNormalFEF)
    (failure : ¬c.HasQuarterLengthBound) {a δ : ℝ} (ha : 0<a) (hδ : 0<δ)
    (fourThirds : IntegrableOn (fun t => (c.physicalInflectionRate t)^(4/3:ℝ)) (Ioi a)) :
    volume {t : ℝ | a<t ∧ 0<c.physicalInflectionRate t ∧ c.physicalInflectionRate t<δ} = ⊤ := by
  by_contra finite
  exact failure (c.quarter_length_of_finite_weak_inflection_duration flow ha hδ fourThirds
    (lt_top_iff_ne_top.mpr finite))

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_finite_weak_inflection_duration
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.weak_inflection_duration_eq_top_of_no_quarter_length
