import LengthGrowth.ActualFlow.ActualForceDissipation
import LengthGrowth.ActualFlow.ForceTailBudget
import LengthGrowth.ActualFlow.ExactInflectionGrowth

noncomputable section
open Set MeasureTheory Function
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem actual_force_weighted_tail_integrable (hf : c.IsNormalFEF) {a : ℝ} (ha : 0<a) :
    IntegrableOn (fun t => c.dissipation t^(-(2/3):ℝ)*c.forceSecondMass t) (Ioi a) :=
  c.force_weighted_tail_integrable hf (fun _ ht => c.actual_force_dissipation_rate hf ht) ha

private theorem eighth_to_budget {g d y : ℝ} (dp : 0<d) (yp : 0≤y)
    (h : g^8≤16*d*y^3) : |g|≤(d+d^(-(2/3):ℝ)*y)^(3/4:ℝ) := by
  let w := d^(-(2/3):ℝ)*y
  have wp : 0≤w := mul_nonneg (Real.rpow_nonneg dp.le _) yp
  have bp : 0≤d+w := add_nonneg dp.le wp
  have e : d*w=d^(1/3:ℝ)*y := by
    dsimp [w]
    rw [←mul_assoc]
    congr 1
    calc
      d * d ^ (-(2/3):ℝ) = d^(1:ℝ)*d^(-(2/3):ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add dp]; norm_num
  have sqb : 4*(d^(1/3:ℝ)*y)≤(d+w)^2 := by nlinarith only [e,sq_nonneg (d-w)]
  have cube := pow_le_pow_left₀ (mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg dp.le _) yp)) sqb 3
  have cubeRoot : (d^(1/3:ℝ))^3=d := by
    rw [←Real.rpow_natCast,←Real.rpow_mul dp.le]
    norm_num
  simp only [mul_pow,cubeRoot,←pow_mul] at cube
  apply le_of_pow_le_pow_left₀ (by decide : (8:ℕ)≠0) (Real.rpow_nonneg bp _)
  rw [Even.pow_abs (show Even 8 by decide),←Real.rpow_natCast ((d+w)^(3/4:ℝ)) 8,←Real.rpow_mul bp]
  norm_num
  calc
    g^8 ≤ 16*d*y^3 := h
    _ = 16*(d*y^3) := by ring
    _ ≤ 4^3*(d*y^3) := mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg dp.le (pow_nonneg yp 3))
    _ ≤ _ := cube

/-- One common integrable budget controls the 4/3 power of the material
angular speed at every label simultaneously on every positive tail. -/
theorem material_angular_tail_budget (hf : c.IsNormalFEF) {a : ℝ} (ha : 0<a) :
    ∃ B : ℝ → ℝ, IntegrableOn B (Ioi a) ∧ ∀t>a, 0≤B t ∧ ∀ u : ℝ,
      |arcDerivative (c.position t) (force (c.position t)) u| ≤ (B t)^(3/4:ℝ) := by
  let B := fun t => c.dissipation t+c.dissipation t^(-(2/3):ℝ)*c.forceSecondMass t
  refine ⟨B,(c.force_dissipation_tail_integrable hf ha).add (c.actual_force_weighted_tail_integrable hf ha),?_⟩
  intro t ht
  have tp := ha.trans ht
  refine ⟨add_nonneg (c.dissipation_nonneg t) (mul_nonneg (Real.rpow_nonneg (c.dissipation_nonneg t) _)
    (c.forceSecondMass_nonneg t)),?_⟩
  intro u
  let v := toIcoMod c.period_pos 0 u
  have hv : v ∈ Icc 0 c.period := Ico_subset_Icc_self (toIcoMod_mem_Ico' c.period_pos u)
  let p := c.regularPositionAt tp.le
  have periodic := arcDerivative_periodic p.smooth p.periodic ((force_smooth p.smooth p.regular).differentiable (by simp))
    (force_periodic p.smooth p.regular p.periodic)
  change Periodic (arcDerivative p.position (force p.position)) c.period at periodic
  have wrap := periodic.sub_zsmul_eq (x:=u) (toIcoDiv c.period_pos 0 u)
  rw [self_sub_toIcoDiv_zsmul] at wrap
  have est := c.material_force_angular_speed tp.le hv
  change arcDerivative p.position (force p.position) v ^8 ≤ _ at est
  rw [show v=toIcoMod c.period_pos 0 u from rfl,wrap] at est
  exact eighth_to_budget (c.force_dissipation_pos tp.le) (c.forceSecondMass_nonneg t) est

private theorem rate_le_of_uniform {t b : ℝ} (hb : 0≤b)
    (h : ∀u : ℝ, |arcDerivative (c.position t) (force (c.position t)) u| ≤ b) :
    c.physicalInflectionRate t ≤ 2*b := by
  unfold physicalInflectionRate
  refine csSup_le (α:=ℝ) ?_ ?_
  · exact ⟨0,Or.inl rfl⟩
  rintro z (rfl|⟨⟨x,y⟩,_,rfl⟩)
  · linarith
  · change arcDerivative (c.position t) (force (c.position t)) y -
      arcDerivative (c.position t) (force (c.position t)) x ≤ 2*b
    linarith only [(abs_le.mp (h x)).1,(abs_le.mp (h y)).2]

/-- The outward angular difference at inflections of every actual smooth
closed flow belongs to L^(4/3) on every positive time tail. -/
theorem physical_inflection_four_thirds_integrable (hf : c.IsNormalFEF) {a : ℝ} (ha : 0<a) :
    IntegrableOn (fun t => (c.physicalInflectionRate t)^(4/3:ℝ)) (Ioi a) := by
  obtain ⟨B,iB,cap⟩ := c.material_angular_tail_budget hf ha
  let g := fun t => if a ≤ t then c.physicalInflectionRate t else 0
  have mg : Measurable g := (c.upperSemicontinuous_physicalInflectionRate_cut ha).measurable
  have ms : AEStronglyMeasurable (fun t => (c.physicalInflectionRate t)^(4/3:ℝ))
      (volume.restrict (Ioi a)) := (mg.pow_const (4/3:ℝ)).aestronglyMeasurable.congr (by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    change a<t at ht
    simp [g,ht.le])
  apply (iB.const_mul ((2:ℝ)^(4/3:ℝ))).mono' ms
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
  obtain ⟨bp,ub⟩ := cap t ht
  have bpos := Real.rpow_nonneg bp (3/4:ℝ)
  have rp := c.physicalInflectionRate_nonneg (ha.trans ht)
  have bound := Real.rpow_le_rpow rp (c.rate_le_of_uniform bpos ub) (by norm_num : (0:ℝ)≤4/3)
  rw [Real.mul_rpow (by norm_num) bpos,←Real.rpow_mul bp] at bound
  norm_num at bound
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg rp _)] using bound

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.material_angular_tail_budget
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.physical_inflection_four_thirds_integrable
