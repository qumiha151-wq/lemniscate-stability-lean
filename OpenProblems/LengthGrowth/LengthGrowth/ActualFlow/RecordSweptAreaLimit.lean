import LengthGrowth.ActualFlow.RecordSweptArea

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Area swept by every traversal and every material label, with absolute Jacobian. -/
def totalSweptArea (t : ℝ) : ℝ := ∫v in 0..t,c.sweptAreaRate v

theorem totalSweptArea_nonneg {t:ℝ} (ht:0≤t) : 0≤c.totalSweptArea t :=
  intervalIntegral.integral_nonneg_of_forall ht c.sweptAreaRate_nonneg

theorem totalSweptArea_record_split (hf : c.IsNormalFEF) {s t:ℝ} (hs:0≤s) (st:s≤t)
    (rec : ∀u∈Icc s t,c.normalizedProduct u≤c.normalizedProduct t) :
    2*Real.pi*(c.totalSweptArea t-c.totalSweptArea s)≤
      c.length t^2*(Real.log (c.energy s)-Real.log (c.energy t)) := by
  have ints (a b : ℝ) (ha : 0≤a) (hb : a≤b) : IntervalIntegrable c.sweptAreaRate volume a b :=
    (c.sweptAreaRate_continuousOn.mono (fun _ h => ha.trans h.1)).intervalIntegrable_of_Icc hb
  have add:=intervalIntegral.integral_add_adjacent_intervals (ints 0 s le_rfl hs) (ints s t hs st)
  unfold totalSweptArea
  rw [←add,add_sub_cancel_left]
  exact c.sweptArea_at_product_record hf hs st rec

/-- A positive limiting bending energy forces the entire area swept since the
initial slice to vanish in units of the squared record length. -/
theorem totalSweptArea_vanishes_at_escaping_records (hf : c.IsNormalFEF)
    (t : ℕ→ℝ) (tt : Tendsto t atTop atTop) (tn : ∀j,0≤t j)
    (rec : ∀j,∀u∈Icc 0 (t j), c.normalizedProduct u≤c.normalizedProduct (t j))
    (escape : Tendsto (fun j=>c.length (t j)) atTop atTop)
    {e:ℝ} (ep : 0<e) (elim : Tendsto c.energy atTop (𝓝 e)) :
    Tendsto (fun j=>c.totalSweptArea (t j)/c.length (t j)^2) atTop (𝓝 0) := by
  have logs : Tendsto (fun v=>Real.log (c.energy v)) atTop (𝓝 (Real.log e)) :=
    (Real.continuousAt_log ep.ne').tendsto.comp elim
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j => ha.trans_le (div_nonneg (c.totalSweptArea_nonneg (tn j))
      (sq_nonneg _)))
  · intro b hb
    have sp : 0<Real.pi*b/2 := by positivity
    obtain ⟨s,hs⟩ := eventually_atTop.1 (logs.eventually_lt_const
      (show Real.log e<Real.log e+Real.pi*b/2 by linarith))
    let s₀:=max 0 s
    have s0p : 0≤s₀ := le_max_left _ _
    have high := hs s₀ (le_max_right _ _)
    have low := (logs.comp tt).eventually_const_lt
      (show Real.log e-Real.pi*b/2<Real.log e by linarith)
    have small : Tendsto (fun j => c.totalSweptArea s₀ / c.length (t j)^2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (n:=2) (by decide)).comp escape)
    filter_upwards [tt.eventually_ge_atTop s₀,low,small.eventually_lt_const
      (show (0:ℝ)<b/2 by linarith)] with j hj hlo hsq
    have Lp:=sq_pos_of_pos (c.length_pos (tn j))
    have bound:=c.totalSweptArea_record_split hf s0p hj
      (fun u hu=>rec j u ⟨s0p.trans hu.1,hu.2⟩)
    have diff : Real.log (c.energy s₀)-Real.log (c.energy (t j))<Real.pi*b := by
      change Real.log e-Real.pi*b/2<Real.log (c.energy (t j)) at hlo
      linarith only [high,hlo]
    have add := mul_lt_mul_of_pos_left diff Lp
    have sPart := (div_lt_iff₀ Lp).mp hsq
    apply (div_lt_iff₀ Lp).mpr
    have sum := mul_lt_mul_of_pos_left sPart (show 0<2*Real.pi by positivity)
    by_contra! bad
    have bad' := mul_le_mul_of_nonneg_left bad (show 0≤2*Real.pi by positivity)
    nlinarith only [bound,add,sum,bad']

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.totalSweptArea_vanishes_at_escaping_records
