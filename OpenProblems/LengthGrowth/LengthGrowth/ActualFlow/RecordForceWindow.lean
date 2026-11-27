import LengthGrowth.ActualFlow.ActualForceDissipation
import LengthGrowth.ActualFlow.ForwardRescaling

noncomputable section
open Set
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- A forward interval for the actual force at a past record of the
energy-length product, in units in which the record energy equals one. -/
theorem actual_record_force_window_unit (flow : c.IsNormalFEF) {s t : ℝ}
    (hs : 0<s) (st : s≤t) (record : ∀u∈Icc 0 s,c.normalizedProduct u≤c.normalizedProduct s)
    (scale : c.energy s=1) (big : 2≤c.length s)
    (window : 2500032*(4/c.length s^2)^(5/3:ℝ)*(t-s)<2/c.length s^2) :
    (∀u∈Icc s t,c.dissipation u<4/c.length s^2) ∧
    1-(4/c.length s^2)*(t-s)≤c.energy t := by
  apply c.record_force_forward_persistence flow hs st record scale big (by norm_num) _ window
  intro u hu du
  have en := (c.energy_le_of_le flow hs.le hu.1.le).trans_eq scale
  have y : 0≤c.forceSecondMass u := intervalIntegral.integral_nonneg_of_forall c.period_pos.le
    (fun _ => mul_nonneg (sq_nonneg _) (norm_nonneg _))
  linarith only [y,c.small_dissipation_rate flow (hs.trans hu.1) en du]

/-- Physical units. A record whose product is H and whose energy is r controls
dissipation and energy on a time window of order H^(4/3)/r^4. -/
theorem actual_record_force_window (flow : c.IsNormalFEF) {s t : ℝ}
    (hs : 0<s) (st : s≤t) (record : ∀u∈Icc 0 s,c.normalizedProduct u≤c.normalizedProduct s)
    (big : 2≤c.normalizedProduct s)
    (window : 2500032*(4/c.normalizedProduct s^2)^(5/3:ℝ)*(c.energy s^4*(t-s))<
      2/c.normalizedProduct s^2) :
    (∀u∈Icc s t,c.dissipation u<(4/c.normalizedProduct s^2)*c.energy s^5) ∧
    (1-(4/c.normalizedProduct s^2)*(c.energy s^4*(t-s)))*c.energy s≤c.energy t := by
  let r := c.energy s
  have hr : 0<r := c.energy_pos hs.le
  have h4 : 0<r^4 := pow_pos hr _
  let b := c.rescaled r 0 hr le_rfl
  have phys (u : ℝ) : 0+(r^4*u)/r^4=u := by rw [zero_add,mul_div_cancel_left₀ _ h4.ne']
  have prod (v : ℝ) : b.normalizedProduct v=c.normalizedProduct (v/r^4) := by
    change b.energy v*b.length v=_
    rw [c.rescaled_energy,c.rescaled_length,zero_add]
    unfold normalizedProduct
    field_simp
  have len : b.length (r^4*s)=c.normalizedProduct s := by
    rw [c.rescaled_length,phys]
    rfl
  have scale : b.energy (r^4*s)=1 := by
    rw [c.rescaled_energy,phys]
    exact div_self hr.ne'
  have scaledRecord (v : ℝ) (hv : v∈Icc 0 (r^4*s)) : b.normalizedProduct v≤b.normalizedProduct (r^4*s) := by
    rw [prod,prod,mul_div_cancel_left₀ _ h4.ne']
    exact record _ ⟨div_nonneg hv.1 h4.le,(div_le_iff₀ h4).2 (by linarith only [hv.2])⟩
  have wn : 2500032*(4/b.length (r^4*s)^2)^(5/3:ℝ)*(r^4*t-r^4*s)<2/b.length (r^4*s)^2 := by
    rw [len,←mul_sub]
    exact window
  obtain ⟨low,keep⟩ := b.actual_record_force_window_unit (c.rescaled_isNormalFEF flow r 0 hr le_rfl)
    (mul_pos h4 hs) (mul_le_mul_of_nonneg_left st h4.le) scaledRecord scale (big.trans len.ge) wn
  rw [len,c.rescaled_energy,phys,←mul_sub] at keep
  refine ⟨?_,(le_div_iff₀ hr).mp keep⟩
  intro u hu
  have h := low (r^4*u) ⟨mul_le_mul_of_nonneg_left hu.1 h4.le,mul_le_mul_of_nonneg_left hu.2 h4.le⟩
  rw [c.rescaled_dissipation,phys,len] at h
  exact (div_lt_iff₀ (pow_pos hr 5)).mp h

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.actual_record_force_window
