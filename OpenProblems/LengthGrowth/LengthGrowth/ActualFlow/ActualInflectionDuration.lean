import LengthGrowth.ActualFlow.AngularSpeedTail
import LengthGrowth.ActualFlow.InflectionSupportDuration

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- A finite total duration of weak outward turning in any one band suffices
for the conjectured length bound of the same flow. -/
theorem quarter_length_of_finite_outward_duration (flow : c.IsNormalFEF) {a δ : ℝ}
    (ha : 0<a) (hd : 0<δ) (duration : volume {t : ℝ | a<t ∧
      0<c.physicalInflectionRate t ∧ c.physicalInflectionRate t<δ} < ⊤) :
    c.HasQuarterLengthBound :=
  c.quarter_length_of_finite_weak_inflection_duration flow ha hd
    (c.physical_inflection_four_thirds_integrable flow ha) duration

/-- The weak outward turning persists for infinite total time on every
positive tail at every threshold in any failure of fourth-root growth. -/
theorem no_quarter_length_requires_infinite_outward_duration (flow : c.IsNormalFEF)
    (failure : ¬c.HasQuarterLengthBound) {a δ : ℝ} (ha : 0<a) (hd : 0<δ) :
    volume {t : ℝ | a<t ∧ 0<c.physicalInflectionRate t ∧ c.physicalInflectionRate t<δ} = ⊤ :=
  c.weak_inflection_duration_eq_top_of_no_quarter_length flow failure ha hd
    (c.physical_inflection_four_thirds_integrable flow ha)

/-- On every positive tail the total angular contribution from rates at or
above any fixed positive threshold is finite, for every genuine flow. -/
theorem high_outward_rate_integrable (flow : c.IsNormalFEF) {a δ : ℝ} (ha : 0<a) (hd : 0<δ) :
    IntegrableOn c.physicalInflectionRate {t : ℝ | a<t ∧ δ≤c.physicalInflectionRate t} := by
  let g := fun t => if a ≤ t then c.physicalInflectionRate t else 0
  let A := {t : ℝ | a<t ∧ δ≤c.physicalInflectionRate t}
  have mg : Measurable g := (c.upperSemicontinuous_physicalInflectionRate_cut ha).measurable
  have eq : A = Ioi a ∩ g ⁻¹' Ici δ := by
    ext t
    by_cases h : a<t
    · simp [A,g,h,h.le]
    · simp [A,h]
  have ma : MeasurableSet A := eq ▸ measurableSet_Ioi.inter (mg measurableSet_Ici)
  have sub : A ⊆ Ioi a := fun _ ht => ht.1
  have ae := ae_restrict_mem (μ:=volume) ma
  have ms : AEStronglyMeasurable c.physicalInflectionRate (volume.restrict A) :=
    mg.aestronglyMeasurable.congr (by filter_upwards [ae] with t ht; exact if_pos ht.1.le)
  apply (((c.physical_inflection_four_thirds_integrable flow ha).mono_set sub).const_mul
    (δ^(1/3:ℝ))⁻¹).mono' ms
  filter_upwards [ae] with t ht
  let P := c.physicalInflectionRate t
  have hP : δ≤P := ht.2
  have pp : 0<P := hd.trans_le hP
  change ‖P‖ ≤ (δ^(1/3:ℝ))⁻¹*P^(4/3:ℝ)
  rw [Real.norm_of_nonneg pp.le,←div_eq_inv_mul]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hd _)).mpr
  calc
    P*δ^(1/3:ℝ) ≤ P*P^(1/3:ℝ) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd.le hP (by norm_num)) pp.le
    _ = P^(4/3:ℝ) := by rw [mul_comm,←Real.rpow_add_one pp.ne']; norm_num

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_finite_outward_duration
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.no_quarter_length_requires_infinite_outward_duration
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.high_outward_rate_integrable
