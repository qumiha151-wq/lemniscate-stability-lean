import LengthGrowth.ActualFlow.TangentFourthIncrement
import LengthGrowth.ActualFlow.TangentTailEquivalence

namespace LengthGrowth.ActualFlow.ForwardImmersion
noncomputable section
open MeasureTheory Set Filter Real TangentSpectrum
open scoped Topology
variable (c : ForwardImmersion)

def tangentQuartic {t : ℝ} (ht : 0≤t) (h : ℝ) : ℝ :=
  quarticIncrement (c.regularPositionAt ht).closedFrenetCurve.unitT h

private theorem unit_period (a : ClosedFrenetCurve) : Function.Periodic a.unitT 1 := by
  intro u
  simpa only [ClosedFrenetCurve.unitT,mul_add,mul_one] using a.tangent_periodic (a.period*u)

theorem tangent_quartic_bounds {t : ℝ} (ht : 0≤t) (h : ℝ) :
    0≤c.tangentQuartic ht h ∧ c.tangentQuartic ht h≤8*h^2*c.normalizedProduct t ∧
      c.tangentQuartic ht h≤16 := by
  let a := (c.regularPositionAt ht).closedFrenetCurve
  have cc : Continuous a.unitT := continuous_iff_continuousAt.mpr fun u=>(a.unitT_der u).continuousAt
  have unit (u : ℝ) : ‖a.unitT u‖=1 := a.tangent_unit _
  have b := increment_sandwich cc unit h
  have up := increment_upper cc (unit_period a) (c.tangent_second_at_every_time ht) h
  change 0≤quarticIncrement a.unitT h ∧ _ ∧ _
  refine ⟨(sq_nonneg _).trans b.1,?_,?_⟩
  · change quarticIncrement a.unitT h≤_
    linarith only [b.2,up]
  · change (∫u in (0:ℝ)..1, ‖a.unitT (u+h)-a.unitT u‖^4)≤16
    have ci : Continuous (fun u => ‖a.unitT (u+h)-a.unitT u‖^4) :=
      ((cc.comp (continuous_id.add continuous_const)).sub cc).norm.pow 4
    have bd := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ)≤1)
      (ci.intervalIntegrable 0 1) (intervalIntegrable_const (c:=(16:ℝ)))
      (fun u _=> (pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans_eq
        (by rw [unit,unit];norm_num : ‖a.unitT (u+h)‖+‖a.unitT u‖=(2:ℝ))) 4).trans_eq (by norm_num))
    simpa using bd

theorem tangent_quartic_at_product_record (hf : c.IsNormalFEF) {t X : ℝ} (ht : 0<t)
    (xp : 0<X) (scale : X^3=c.normalizedProduct t)
    (record : ∀s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) :
    let h := 1/(64*X^2)
    h/4194304 ≤ c.tangentQuartic ht.le h := by
  let a := (c.regularPositionAt ht.le).closedFrenetCurve
  have cc : Continuous a.unitT := continuous_iff_continuousAt.mpr fun u=>(a.unitT_der u).continuousAt
  have unit (u : ℝ) : ‖a.unitT u‖=1 := a.tangent_unit _
  obtain ⟨_,two,M,four,cap⟩ := c.signed_fourier_at_record hf ht xp scale record
  exact (increment_lower cc (unit_period a) xp two four cap).trans (increment_sandwich cc unit _).1

/-- For any prescribed lag cutoff and product and time lower bounds, failure
of the fourth-root rate forces a record with a geometric tangent increment. -/
theorem small_lags_at_high_records (hf : c.IsNormalFEF) (fail : ¬c.HasQuarterLengthBound)
    {δ : ℝ} (dp : 0<δ) (A t₀ : ℝ) :
    ∃t,∃ht : 0<t, t₀<t ∧ A<c.normalizedProduct t ∧
      (∀s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) ∧
      ∃h : ℝ, 0<h ∧ h<δ ∧ h/4194304≤c.tangentQuartic ht.le h := by
  let B:=max 1 (1/δ)
  obtain ⟨t,late,ht,large,rec,_⟩ := c.high_record_cubic_half_of_failure hf fail (max A (B^3)) t₀
  let U := c.normalizedProduct t
  have up : 0<U := mul_pos (c.energy_pos ht.le) (c.length_pos ht.le)
  let X := U^(1/3:ℝ)
  have xp : 0<X := Real.rpow_pos_of_pos up _
  have xs : X^3=U := by
    dsimp only [X]
    rw [←Real.rpow_natCast,←Real.rpow_mul up.le]
    norm_num
  have xb : B<X := by
    by_contra! hn
    have hp := pow_le_pow_left₀ xp.le hn 3
    rw [xs] at hp
    exact (not_le_of_gt ((le_max_right A (B^3)).trans_lt large)) hp
  have x1 : 1<X := (le_max_left _ _).trans_lt xb
  have xd : 1<δ*X := by
    have h : 1/δ<X := (le_max_right _ _).trans_lt xb
    simpa only [mul_comm] using (div_lt_iff₀ dp).mp h
  have xx : X≤64*X^2 := by nlinarith [mul_nonneg xp.le (sub_nonneg.mpr x1.le),sq_nonneg X]
  have sm : 1/(64*X^2)<δ := (div_lt_iff₀ (by positivity)).mpr
    (xd.trans_le (mul_le_mul_of_nonneg_left xx dp.le))
  exact ⟨t,ht,late,(le_max_left _ _).trans_lt large,rec,1/(64*X^2),by positivity,sm,
    c.tangent_quartic_at_product_record hf ht xp xs rec⟩

end
end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.small_lags_at_high_records
