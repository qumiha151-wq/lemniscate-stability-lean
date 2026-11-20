import SolitonClassification.FrozenUniformEscape

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.FrozenStress
variable {X : Type*} [TopologicalSpace X]

private theorem fixed_time_corrected_continuous (Z : X→Orbit) {t : ℝ}
    (hk : Continuous (fun c => (Z c).k t)) (hv : Continuous (fun c => (Z c).v t))
    (hp : Continuous (fun c => (Z c).p t)) (hq : Continuous (fun c => (Z c).q t))
    (ha : ∀c, 0<(Z c).amplitude t) : Continuous (fun c => (Z c).outgoingHeight t) := by
  have cA : Continuous (fun c => (Z c).amplitude t) :=
    Real.continuous_sqrt.comp ((((hk.pow 2).div_const 2).pow 2).add (hv.pow 2))
  have cr : Continuous (fun c => (Z c).root t) := Real.continuous_sqrt.comp cA
  have cH : Continuous (fun c => (Z c).radial t) := (((hk.pow 2).div_const 2).mul hq).add (hv.mul hp)
  have cB : Continuous (fun c => (Z c).transverse t) := (((hk.pow 2).div_const 2).mul hp).sub (hv.mul hq)
  have rne (c : X) : (Z c).root t≠0 := (Real.sqrt_pos.mpr (ha c)).ne'
  have cU : Continuous (fun c => (Z c).shape t) := hk.div cr rne
  have cw : Continuous (fun c => (Z c).slope t) := hv.div cA (fun c => (ha c).ne')
  have ca : Continuous (fun c => (Z c).along t) := cH.div cA (fun c => (ha c).ne')
  have cb : Continuous (fun c => (Z c).across t) := cB.div cA (fun c => (ha c).ne')
  have chiC : Continuous (fun c => chi ((Z c).shape t) ((Z c).slope t) ((Z c).along t) ((Z c).across t)) := by
    unfold chi
    fun_prop
  exact ((cr.pow 2).mul ca).neg.sub (chiC.div cr rne)

private theorem height_time_control (z : Orbit) {S : ℝ} (ha : ∀t≥S,12≤z.amplitude t) {x y : ℝ}
    (hx : S≤x) (hy : S≤y) :
    |x-y|≤4*|z.outgoingHeight x-z.outgoingHeight y| := by
  have ordered (u v : ℝ) (hu : S≤u) (uv : u<v) : v-u≤4*(z.outgoingHeight v-z.outgoingHeight u) := by
    have df (t : ℝ) (ht : t∈Icc u v) : DifferentiableAt ℝ z.outgoingHeight t :=
      (z.corrected_outgoing_rate t (by linarith [ha t (hu.trans ht.1)])).differentiableAt
    obtain ⟨t,ht,eq⟩ := exists_deriv_eq_slope z.outgoingHeight uv (fun x hx => (df x hx).continuousAt.continuousWithinAt)
      (fun x hx => (df x ⟨hx.1.le,hx.2.le⟩).differentiableWithinAt)
    have lo := (le_div_iff₀ (sub_pos.mpr uv)).mp
      ((z.large_amplitude_height (ha t (hu.trans ht.1.le))).2.trans_eq eq)
    linarith
  rcases lt_trichotomy x y with xy|eq|yx
  · rw [abs_of_nonpos (sub_nonpos.mpr xy.le),abs_sub_comm (z.outgoingHeight x)]
    linarith only [ordered x y hx xy,le_abs_self (z.outgoingHeight y-z.outgoingHeight x)]
  · simp [eq]
  · rw [abs_of_nonneg (sub_nonneg.mpr yx.le)]
    linarith only [ordered y x hy yx,le_abs_self (z.outgoingHeight x-z.outgoingHeight y)]

/-- For any compact family of genuine seam trajectories, every sufficiently
high corrected outgoing section has a continuous hitting time. Only continuity
of the original four state variables at fixed times is used. -/
theorem continuous_corrected_seam_crossing [CompactSpace X] (Z : X→Orbit)
    (zero : ∀c,(Z c).radial 0=0) (p0 : ∀c,(Z c).p 0=1)
    (hk : ∀t,Continuous (fun c => (Z c).k t)) (hv : ∀t,Continuous (fun c => (Z c).v t))
    (hp : ∀t,Continuous (fun c => (Z c).p t)) (hq : ∀t,Continuous (fun c => (Z c).q t))
    (minTime : ℝ := 0) :
    ∃S≥minTime, ∃H₀ : ℝ, ∀H≥H₀, ∃τ : X→ℝ, Continuous τ ∧ ∀c,
      S≤τ c ∧ (Z c).outgoingHeight (τ c)=H ∧ 1/4≤deriv (Z c).outgoingHeight (τ c) ∧
        ∀t≥S,(Z c).outgoingHeight t=H → t=τ c := by
  have cr (t : ℝ) : Continuous (fun c => (Z c).radial t) :=
    ((((hk t).pow 2).div_const 2).mul (hq t)).add ((hv t).mul (hp t))
  obtain ⟨S',_,raw'⟩ := uniform_seam_entrance Z zero p0 cr 12
  let S := max S' minTime
  have sp : S≥minTime := le_max_right .. 
  have raw (c : X) (t : ℝ) (ht : S≤t) := raw' c t ((le_max_left ..).trans ht)
  have high (c : X) (t : ℝ) (ht : S≤t) : 12≤(Z c).amplitude t := by
    have nn : 0≤(Z c).amplitude t := Real.sqrt_nonneg _
    have ra : -(Z c).radial t≤(Z c).amplitude t := by nlinarith [(Z c).stress_unit t,sq_nonneg ((Z c).transverse t)]
    exact (raw c t ht).le.trans ra
  have cc (t : ℝ) (ht : S≤t) : Continuous (fun c => (Z c).outgoingHeight t) :=
    fixed_time_corrected_continuous Z (hk t) (hv t) (hp t) (hq t) (fun c => by linarith [high c t ht])
  obtain ⟨H₀,Hb⟩ := (isCompact_range (cc S le_rfl)).bddAbove
  refine ⟨S,sp,H₀,?_⟩
  intro H hH
  have existsTime (c : X) : ∃t≥S,(Z c).outgoingHeight t=H := by
    obtain ⟨_,_,_,grow,_⟩ := (Z c).seam_corrected_sections (zero c) (p0 c)
    obtain ⟨T,st,hi⟩ := ((eventually_ge_atTop S).and (grow.eventually_ge_atTop H)).exists
    have ct : ContinuousOn (Z c).outgoingHeight (Icc S T) := fun x hx =>
      ((Z c).corrected_outgoing_rate x (by linarith [high c x hx.1])).continuousAt.continuousWithinAt
    have lo := (Hb (mem_range_self c)).trans hH
    obtain ⟨x,hx,eq⟩ := intermediate_value_Icc st ct (show H∈Icc ((Z c).outgoingHeight S)
      ((Z c).outgoingHeight T) from ⟨lo,hi⟩)
    exact ⟨x,hx.1,eq⟩
  choose τ late hit using existsTime
  refine ⟨τ,continuous_iff_continuousAt.mpr (fun c => ?_),fun c => ⟨late c,hit c,
    ((Z c).large_amplitude_height (high c _ (late c))).2,?_⟩⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε ep
    have lim := (cc (τ c) (late c)).continuousAt (x:=c)
    have nb := Metric.tendsto_nhds.mp lim (ε/4) (by positivity)
    filter_upwards [nb] with d hd
    have lb := height_time_control (Z d) (high d) (late d) (late c)
    rw [hit d,abs_sub_comm H ((Z d).outgoingHeight (τ c))] at lb
    rw [Real.dist_eq,hit c] at hd
    rw [Real.dist_eq]
    linarith
  · intro t ht eq
    have bd := height_time_control (Z c) (high c) ht (late c)
    rw [eq,hit c,sub_self,abs_zero,mul_zero] at bd
    exact sub_eq_zero.mp (abs_nonpos_iff.mp bd)

end ClosedSimilarity.FrozenStress
#print axioms ClosedSimilarity.FrozenStress.continuous_corrected_seam_crossing
