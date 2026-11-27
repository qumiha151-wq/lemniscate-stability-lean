import LengthGrowth.ActualFlow.PhysicalCurvatureExcursion

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

private theorem small_mean_excludes_cap {μ d : ℝ}
    (small : |μ| < (2-(2*d^2+d))/(|2*d^2-1|+1)) :
    2*(1+μ)*d^2+d < 2+μ := by
  have den : 0 < |2*d^2-1|+1 := by positivity
  have b := (lt_div_iff₀ den).mp small
  have z : μ*(2*d^2-1) ≤ |μ| * |2*d^2-1| := by rw [← abs_mul]; exact le_abs_self _
  linarith only [show 2*(1+μ)*d^2+d-(2+μ)=2*d^2+d-2+μ*(2*d^2-1) by ring,
    z, b, abs_nonneg μ, show |μ| * (|2*d^2-1|+1)=|μ| * |2*d^2-1|+|μ| by ring]

/-- Any failure of the individual fourth-root upper bound forces both
directions to exceed d times the RMS curvature on a common arbitrarily
late, arbitrarily high product record, for every 2d²+d<2. -/
theorem high_record_both_curvature_excursions (hf : c.IsNormalFEF)
    (failure : ¬c.HasQuarterLengthBound) (K T : ℝ) {d : ℝ} (gap : 2*d^2+d<2) :
    ∃ t, T<t ∧ K<c.normalizedProduct t ∧
      (∀ s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) ∧
      (∃ u,curvature (c.position t) u < -d*c.rmsCurvature t) ∧
      (∃ u,d*c.rmsCurvature t < curvature (c.position t) u) := by
  let ε := min (1/2:ℝ) ((2-(2*d^2+d))/(|2*d^2-1|+1))
  have ep : 0<ε := lt_min (by norm_num) (div_pos (sub_pos.mpr gap) (by positivity))
  let S := materialSignedCurvature (c.position 0) c.period
  obtain ⟨t,ht,ht0,hu,rec,_⟩ := c.high_record_cubic_half_of_failure hf failure
    (max K ((|S|/ε)^2/2)) T
  have lp := c.length_pos ht0.le
  have enr := c.energy_pos ht0.le
  let m := c.rmsCurvature t
  have mp : 0<m := Real.sqrt_pos.mpr (by positivity)
  have ms : c.length t*m^2=2*c.energy t := by
    dsimp only [m,rmsCurvature]
    rw [Real.sq_sqrt (by positivity),mul_div_cancel₀ _ lp.ne']
  have scaleSq : (c.length t*m)^2=2*c.normalizedProduct t := by
    change _=2*(c.energy t*c.length t)
    nlinarith only [congrArg (fun z:ℝ=>z*c.length t) ms]
  have mem : |S|/ε<c.length t*m := by
    by_contra! le
    have sq := pow_le_pow_left₀ (mul_pos lp mp).le le 2
    rw [scaleSq] at sq
    linarith [le_max_right K ((|S|/ε)^2/2)]
  have rat : |S|/(c.length t*m)<ε := by
    apply (div_lt_iff₀ (mul_pos lp mp)).mpr
    linarith [(div_lt_iff₀ ep).mp mem]
  have rate : 0≤deriv c.normalizedProduct t := by
    have h := c.normalizedProduct_hasDerivAt_normal hf ht0
    rw [h.deriv]
    apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp h).1
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds ht0)] with s hst sp
    rw [slope_def_field]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr (rec s ⟨sp.le,hst.le⟩)) (sub_nonpos.mpr hst.le)
  have excursion (r:ℝ) (absr : |r|=m) : ∃u,curvature (c.position t) u/r < -d := by
    by_contra! floor
    have rn : r≠0 := by intro hr; rw [hr,abs_zero] at absr; linarith
    have rsq : r^2=m^2 := by rw [←absr,sq_abs]
    have hb : |materialSignedCurvature (c.position t) c.period/(c.length t*r)| < ε := by
      rw [c.signedCurvature_eq_initial ht0.le,abs_div,abs_mul,abs_of_pos lp,absr]
      exact rat
    let μ := materialSignedCurvature (c.position t) c.period/(c.length t*r)
    have mub : μ<1 := by
      have hμ : μ<ε := (le_abs_self μ).trans_lt hb
      have lim : ε≤1/2 := min_le_left .. 
      linarith
    have cone := c.actual_signed_excursion_constraint hf ht0 rn (by rw [rsq,ms]) rate floor mub
    have impossible := small_mean_excludes_cap (d:=d) (μ:=μ) (hb.trans_le (min_le_right ..))
    exact impossible.not_ge cone
  obtain ⟨u,hu'⟩ := excursion m (abs_of_pos mp)
  obtain ⟨v,hv'⟩ := excursion (-m) (by rw [abs_neg,abs_of_pos mp])
  have hv := (div_lt_iff_of_neg (neg_neg_of_pos mp)).mp hv'
  exact ⟨t,ht,(le_max_left ..).trans_lt hu,rec,⟨u,(div_lt_iff₀ mp).mp hu'⟩,
    ⟨v,by change d*m<_;nlinarith only [hv]⟩⟩

/-- At any fixed admissible fraction, eventual avoidance of the two
simultaneous excursions at high records implies the requested bound. -/
theorem quarter_length_of_high_record_excursion_cap (hf : c.IsNormalFEF)
    (K T : ℝ) {d : ℝ} (gap : 2*d^2+d<2)
    (barrier : ∀ t,T<t → K<c.normalizedProduct t →
      (∀ s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) →
      (∀ u,-d*c.rmsCurvature t≤curvature (c.position t) u) ∨
      (∀ u,curvature (c.position t) u≤d*c.rmsCurvature t)) : c.HasQuarterLengthBound := by
  by_contra failure
  obtain ⟨t,ht,hu,rec,⟨u,low⟩,⟨v,high⟩⟩ := c.high_record_both_curvature_excursions hf failure K T gap
  rcases barrier t ht hu rec with left|right
  · exact low.not_ge (left u)
  · exact high.not_ge (right v)
end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.high_record_both_curvature_excursions
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_high_record_excursion_cap
