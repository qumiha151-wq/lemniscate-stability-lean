import LengthGrowth.ActualFlow.RecordDissipationSpike

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c:ForwardImmersion)

/-- A lower dissipation bound throughout the interval gives a loss in the actual
endpoint energies, including intervals starting at zero. -/
theorem relative_drop_on_force_window (hf:c.IsNormalFEF) {s h rate:ℝ}
    (hs:0≤s) (hn:0≤h)
    (floor:∀u∈Icc s (s+h),rate*c.energy s≤c.dissipation u) :
    c.energy (s+h)≤(1-h*rate)*c.energy s := by
  have st : s≤s+h := by linarith
  have sub : Icc s (s+h)⊆Ici 0 := fun _ hu=>hs.trans hu.1
  have v:=intervalIntegral.integral_mono_on (μ:=volume) st
    (intervalIntegrable_const (c:=rate*c.energy s))
    ((c.dissipation_continuousOn.mono sub).intervalIntegrable_of_Icc st) floor
  have loss:=c.energy_add_integral_dissipation hf hs st
  rw [intervalIntegral.integral_const,smul_eq_mul] at v
  nlinarith only [v,loss]

/-- A nonincreasing regularly varying energy loses a vanishing relative fraction
on all time intervals whose size is little-o of their starting times. -/
theorem regularly_varying_short_window (hf:c.IsNormalFEF) {p:ℝ}
    (law:∀r:ℝ,1<r→Tendsto (fun t=>c.energy (r*t)/c.energy t) atTop (𝓝 (r^p)))
    (t h:ℕ→ℝ) (tpos:∀j,0<t j) (hpos:∀j,0≤h j) (late:Tendsto t atTop atTop)
    (short:Tendsto (fun j=>h j/t j) atTop (𝓝 0)) :
    Tendsto (fun j=>c.energy (t j+h j)/c.energy (t j)) atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have cont : ContinuousAt (fun r:ℝ=>r^p) 1 := continuousAt_id.rpow_const (Or.inl one_ne_zero)
    have lim : Tendsto (fun r:ℝ=>r^p) (𝓝[>] 1) (𝓝 1) := by
      simpa using cont.tendsto.mono_left nhdsWithin_le_nhds
    obtain ⟨r,ar,one⟩ := ( (lim.eventually_const_lt ha).and
      (self_mem_nhdsWithin (a:=(1:ℝ)) (s:=Ioi 1)) ).exists
    have sz:=short.eventually_lt_const (show 0<r-1 by linarith [show 1<r from one])
    have lo:=((law r one).comp late).eventually_const_lt ar
    filter_upwards [sz,lo] with j bound low
    have inc : t j+h j≤r*t j := by
      have v:=(div_lt_iff₀ (tpos j)).mp bound
      linarith only [v]
    have e:=c.energy_le_of_le hf (by linarith [tpos j,hpos j] : 0≤t j+h j) inc
    exact low.trans_le (div_le_div_of_nonneg_right e (c.energy_pos (tpos j).le).le)
  · intro a ha
    apply Eventually.of_forall
    intro j
    have e:=c.energy_le_of_le hf (tpos j).le (by linarith [hpos j] : t j≤t j+h j)
    exact ((div_le_one (c.energy_pos (tpos j).le)).mpr e).trans_lt ha

end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.regularly_varying_short_window
