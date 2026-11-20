import LengthGrowth.ActualFlow.AmbientMaterial
import LengthGrowth.ActualFlow.PhysicalTimeAverage
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! A thin strip can have arbitrary direction and unbounded longitudinal extent. -/
noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve

/-- Some curvature must turn the tangent away from the transverse direction
within four strip half-widths. The same material point need not work for
different strips. -/
theorem exists_curvature_in_strip (c : ClosedFrenetCurve) {z : ℂ} (hz : ‖z‖ = 1)
    {r h : ℝ} (hr : 0 < r) (hstrip : ∀ s, |(z*c.curve s).im - h| ≤ r) :
    ∃ s, 1 ≤ (8*r)*|c.curvature s| := by
  let X := fun s => (z*c.curve s).re
  let Y := fun s => (z*c.curve s).im
  let U := fun s => (z*c.tangent s).re
  let V := fun s => (z*c.tangent s).im
  let A := fun s => (z*((c.curvature s : ℂ)*(Complex.I*c.tangent s))).im
  have hX (s : ℝ) : HasDerivAt X (U s) s :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt s ((c.curve_deriv s).const_mul z)
  have hY (s : ℝ) : HasDerivAt Y (V s) s :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt s ((c.curve_deriv s).const_mul z)
  have hV (s : ℝ) : HasDerivAt V (A s) s :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt s ((c.tangent_deriv s).const_mul z)
  have cont {f g : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (g s) s) : Continuous f :=
    continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  obtain ⟨s, _, hs⟩ := exists_hasDerivAt_eq_slope X U c.period_pos
    (cont hX).continuousOn (fun y _ => hX y)
  have hper : X c.period = X 0 := by
    dsimp [X]; rw [show c.curve c.period = c.curve 0 by simpa using c.curve_periodic 0]
  rw [hper, sub_self, zero_div] at hs
  have hu := Complex.normSq_eq_norm_sq (z*c.tangent s)
  rw [Complex.normSq_apply, norm_mul, hz, c.tangent_unit, one_mul] at hu
  change U s * U s + V s * V s = _ at hu
  have hone : |V s| = 1 := by
    rw [hs] at hu
    nlinarith [sq_abs (V s), abs_nonneg (V s)]
  let e := s + 4*r
  have hse : s < e := by dsimp [e]; linarith
  obtain ⟨v, hv, heq⟩ := exists_hasDerivAt_eq_slope Y V hse
    (cont hY).continuousOn (fun y _ => hY y)
  have hYdiff : |Y e-Y s| ≤ 2*r := by
    obtain ⟨ha,hb⟩ := abs_le.mp (hstrip s)
    obtain ⟨hc,hd⟩ := abs_le.mp (hstrip e)
    dsimp [Y]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsmall : |V v| ≤ 1/2 := by
    rw [heq, abs_div, abs_of_pos (sub_pos.mpr hse)]
    apply (div_le_iff₀ (sub_pos.mpr hse)).mpr
    dsimp [e]; linarith
  obtain ⟨w, _, hw⟩ := exists_hasDerivAt_eq_slope V A hv.1
    (cont hV).continuousOn (fun y _ => hV y)
  have hdist : 1/2 ≤ |V v - V s| := by
    have ht := abs_sub_abs_le_abs_sub (V s) (V v)
    rw [abs_sub_comm (V s) (V v), hone] at ht
    linarith
  have hA : |A w| ≤ |c.curvature w| := by
    apply (Complex.abs_im_le_norm _).trans
    simp [hz, c.tangent_unit]
  have hh := congrArg abs ((eq_div_iff (sub_pos.mpr hv.1).ne').mp hw)
  rw [abs_mul, abs_of_pos (sub_pos.mpr hv.1)] at hh
  have hh' := mul_le_mul hA (show v-s ≤ 4*r by dsimp [e] at hv; linarith [hv.2])
    (sub_nonneg.mpr hv.1.le) (abs_nonneg _)
  exact ⟨w, by linarith⟩

end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The actual image is contained in a Euclidean strip of half-width R/E(t). -/
def FitsEnergyStrip (R t : ℝ) : Prop :=
  ∃ (z : ℂ) (h : ℝ), ‖z‖ = 1 ∧ ∀ u, |(z*c.position t u).im-h| ≤ R/c.energy t

/-- Strip times form a compact set on each compact forward time interval,
including when the chosen direction and center jump. -/
theorem isCompact_strip_times {T : ℝ} (hT : 0≤T) (R : ℝ) :
    IsCompact {x ∈ Icc 0 T | c.FitsEnergyStrip R x} := by
  have sub : Icc 0 T ⊆ Ici 0 := fun _ hx => hx.1
  have cp (u : ℝ) : ContinuousOn (fun t => c.position t u) (Icc 0 T) := by
    have hj : ContinuousOn (fun z : ℝ × ℝ => c.position z.1 z.2) (Ici 0 ×ˢ univ) := by
      simpa only [iteratedDeriv_zero] using c.spatial_jets_continuous 0 (by decide)
    exact hj.comp (continuous_id.prodMk (continuous_const (y:=u))).continuousOn
      (fun _ ht => ⟨sub ht,mem_univ _⟩)
  have cr : ContinuousOn (fun t => R/c.energy t) (Icc 0 T) :=
    continuousOn_const.div (c.energy_continuousOn.mono sub) (fun t ht => (c.energy_pos ht.1).ne')
  obtain ⟨t₀,_,hm⟩ := isCompact_Icc.exists_isMaxOn ⟨0,le_rfl,hT⟩ ((cp 0).norm.add cr)
  let M := ‖c.position t₀ 0‖+R/c.energy t₀
  let K : Set (ℝ × ℂ × ℝ) := Icc 0 T ×ˢ (Metric.sphere 0 1 ×ˢ Icc (-M) M)
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_sphere 0 1).prod isCompact_Icc)
  let F (u : ℝ) := {v ∈ K | |(v.2.1*c.position v.1 u).im-v.2.2| ≤ R/c.energy v.1}
  have ht (v : ℝ × ℂ × ℝ) (hv : v ∈ K) : v.1 ∈ Icc 0 T := hv.1
  have hF (u : ℝ) : IsClosed (F u) := by
    have hz : ContinuousOn (fun v : ℝ × ℂ × ℝ => v.2.1) K := (continuous_fst.comp continuous_snd).continuousOn
    have hh : ContinuousOn (fun v : ℝ × ℂ × ℝ => v.2.2) K := (continuous_snd.comp continuous_snd).continuousOn
    have hp := (cp u).comp continuous_fst.continuousOn ht
    exact hK.isClosed.isClosed_le ((Complex.continuous_im.comp_continuousOn (hz.mul hp)).sub hh).abs
      (cr.comp continuous_fst.continuousOn ht)
  have hcomp : IsCompact (⋂ u, F u) := hK.of_isClosed_subset (isClosed_iInter hF)
    (fun _ hv => (mem_iInter.mp hv 0).1)
  convert! hcomp.image continuous_fst using 1
  ext t
  constructor
  · rintro ⟨ht',z,h,hz,ha⟩
    have h0 := abs_le.mp (ha 0)
    have hv : |(z*c.position t 0).im| ≤ ‖c.position t 0‖ := by
      simpa [hz] using Complex.abs_im_le_norm (z*c.position t 0)
    have hmax : ‖c.position t 0‖+R/c.energy t ≤ M := hm ht'
    have hK' : (t,z,h) ∈ K := ⟨ht', by simpa [Metric.mem_sphere,dist_zero_right] using hz,
      by linarith [(abs_le.mp hv).1,h0.2], by linarith [(abs_le.mp hv).2,h0.1]⟩
    exact ⟨(t,z,h),mem_iInter.mpr (fun u => ⟨hK',ha u⟩),rfl⟩
  · rintro ⟨⟨s,z,h⟩,hv,rfl⟩
    have hK' := (mem_iInter.mp hv 0).1
    exact ⟨hK'.1,z,h, by simpa [Metric.mem_sphere,dist_zero_right] using hK'.2.1,
      fun u => (mem_iInter.mp hv u).2⟩

theorem strip_forces_dissipation {R t : ℝ} (hR : 0<R) (ht : 0≤t)
    (h : c.FitsEnergyStrip R t) :
    1 / (16777216*(8*R)^6) ≤ c.normalizedDissipation t := by
  obtain ⟨z,b,hz,hstrip⟩ := h
  let a := c.regularPositionAt ht
  have he := c.energy_pos ht
  obtain ⟨s,hs⟩ := a.closedFrenetCurve.exists_curvature_in_strip hz (div_pos hR he)
    (h:=b) (fun s => hstrip (a.arclengthInverse s))
  let u := a.arclengthInverse s
  rw [a.closedFrenetCurve_curvature] at hs
  change 1 ≤ 8*(R/c.energy t)*|curvature (c.position t) u| at hs
  have heq : 8*(R/c.energy t)*|curvature (c.position t) u| =
      (8*R)*(|curvature (c.position t) u|/c.energy t) := by ring
  rw [heq] at hs
  have h6 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hs 6
  rw [one_pow, mul_pow] at h6
  have hd := c.normalized_curvature_six_le ht u
  have hprod := mul_le_mul_of_nonneg_left hd (pow_nonneg (by positivity : 0≤8*R) 6)
  apply (div_le_iff₀ (by positivity : 0<16777216*(8*R)^6)).mpr
  dsimp [normalizedDissipation]
  linarith only [h6,hprod,show (8*R)^6*(16777216*(c.dissipation t/c.energy t^5)) =
    (c.dissipation t/c.energy t^5)*(16777216*(8*R)^6) by ring]

theorem fits_strip_of_bounded_energyLength (h : c.HasBoundedEnergyLength) :
    ∃ R : ℝ, 0<R ∧ ∀ t, 0≤t → c.FitsEnergyStrip R t := by
  obtain ⟨K,hK⟩ := h
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun t ht => ?_⟩
  let a := c.regularPositionAt ht
  let b := a.closedFrenetCurve
  refine ⟨1,(b.curve 0).im, norm_one, fun u => ?_⟩
  obtain ⟨s,hs,hs'⟩ := b.curve_periodic.exists_mem_Ico₀ b.period_pos (a.arclength u)
  have hu : b.curve (a.arclength u) = c.position t u := by
    change a.position (a.arclengthInverse (a.arclength u)) = a.position u
    rw [a.arclength_inverse_right]
  rw [one_mul, ← hu, hs', ← Complex.sub_im]
  apply (Complex.abs_im_le_norm _).trans
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => b.curve_deriv y)
    (b.tangent_continuous.intervalIntegrable 0 s)
  rw [← hi]
  calc
    _ ≤ ∫ y in 0..s, ‖b.tangent y‖ := intervalIntegral.norm_integral_le_integral_norm hs.1
    _ = s := by simp [b.tangent_unit]
    _ ≤ b.period := hs.2.le
    _ ≤ _ := (le_div_iff₀ (c.energy_pos ht)).mpr (by
      change c.length t * c.energy t ≤ max 1 K
      rw [mul_comm]; exact (hK t ht).trans (le_max_right _ _))

/-- The elapsed-time cost of any collection of times with high normalized
dissipation. Lebesgue outer measure makes the statement applicable to an
arbitrary, possibly changing choice of enclosing strip. -/
theorem occupation_le_dissipation {T δ : ℝ} (hT : 0≤T) (hδ : 0≤δ) (A : Set ℝ)
    (htimes : ∀ x ∈ A, x ∈ Icc 0 T ∧ δ ≤ c.normalizedDissipation x) :
    δ*volume.real A ≤ ∫ x in 0..T, c.normalizedDissipation x := by
  let B := {x ∈ Icc 0 T | δ ≤ c.normalizedDissipation x}
  have sub : B ⊆ Icc 0 T := fun _ hx => hx.1
  have hc := c.normalizedDissipation_continuousOn.mono (show Icc 0 T ⊆ Ici 0 from fun _ hx => hx.1)
  have hm : MeasurableSet B := (isClosed_Icc.isClosed_le continuousOn_const hc).measurableSet
  have hfin : volume B ≠ ⊤ := (lt_of_le_of_lt (measure_mono sub) isCompact_Icc.measure_lt_top).ne
  have hi : IntegrableOn c.normalizedDissipation (Icc 0 T) volume :=
    hc.integrableOn_compact isCompact_Icc
  have hend := setIntegral_mono_on (μ := volume) (f := fun _ => δ) (g := c.normalizedDissipation)
    (integrableOn_const hfin) (hi.mono_set sub) hm (fun _ hx => hx.2)
  have hnon (x : ℝ) : 0 ≤ c.normalizedDissipation x :=
    div_nonneg (c.dissipation_nonneg _) (pow_nonneg (c.energy_nonneg _) _)
  have hmono := setIntegral_mono_set hi (Filter.Eventually.of_forall hnon) (Filter.Eventually.of_forall sub)
  calc
    _ ≤ δ*volume.real B := mul_le_mul_of_nonneg_left (measureReal_mono (show A ⊆ B from htimes) hfin) hδ
    _ = ∫ _ in B, δ := by simp [mul_comm]
    _ ≤ _ := hend
    _ ≤ ∫ x in Icc 0 T, c.normalizedDissipation x := hmono
    _ = _ := by rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hT]

/-- An explicit time budget for strip containment over a finite horizon. -/
theorem strip_time_energy_budget (hflow : c.IsNormalFEF) {R T : ℝ} (hR : 0<R) (hT : 0≤T) :
    4*(1/(16777216*(8*R)^6))*volume.real {x ∈ Icc 0 T | c.FitsEnergyStrip R x} ≤
      (c.energy T)⁻¹^4 - (c.energy 0)⁻¹^4 := by
  have hocc := c.occupation_le_dissipation hT (by positivity : 0 ≤ 1/(16777216*(8*R)^6))
    {x ∈ Icc 0 T | c.FitsEnergyStrip R x} (fun x hx => ⟨hx.1,c.strip_forces_dissipation hR hx.1.1 hx.2⟩)
  linarith only [hocc,c.inverse_fourth_physical_time hflow (s:=0) le_rfl hT,
    show 4*(1/(16777216*(8*R)^6))*volume.real {x ∈ Icc 0 T | c.FitsEnergyStrip R x} =
      4*((1/(16777216*(8*R)^6))*volume.real {x ∈ Icc 0 T | c.FitsEnergyStrip R x}) by ring]

theorem exists_small_strip_occupation (hflow : c.IsNormalFEF) (hnot : ¬c.HasQuarterLengthBound)
    {R ε : ℝ} (hR : 0<R) (hε : 0<ε) (S : ℝ) :
    ∃ T, max S 1 < T ∧ volume.real {x ∈ Icc 0 T | c.FitsEnergyStrip R x} < ε*T := by
  let δ := 1/(16777216*(8*R)^6)
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨T,hT,hmean⟩ := c.exists_small_average_of_not_quarter hflow hnot (mul_pos hδ hε) S
  have ht : 0 ≤ T := zero_le_one.trans ((le_max_right S 1).trans hT.le)
  have hocc := c.occupation_le_dissipation ht hδ.le {x ∈ Icc 0 T | c.FitsEnergyStrip R x}
    (fun x hx => ⟨hx.1,c.strip_forces_dissipation hR hx.1.1 hx.2⟩)
  refine ⟨T,hT, (lt_of_mul_lt_mul_left ?_ hδ.le)⟩
  rw [← mul_assoc]; exact hocc.trans_lt hmean

/-- The strip can change its center and direction independently at every
time. Positive lower time density suffices for the global length estimate. -/
theorem quarter_length_iff_strip_frequency (hflow : c.IsNormalFEF) :
    c.HasQuarterLengthBound ↔ ∃ R η S : ℝ, 0<R ∧ 0<η ∧ ∀ T, S≤T →
      η*T ≤ volume.real {x ∈ Icc 0 T | c.FitsEnergyStrip R x} := by
  constructor
  · intro h
    obtain ⟨R,hR,ha⟩ := c.fits_strip_of_bounded_energyLength (c.bounded_energyLength_of_quarter_length hflow h)
    refine ⟨R,1,0,hR,zero_lt_one,fun T hT => ?_⟩
    have heq : {x ∈ Icc 0 T | c.FitsEnergyStrip R x} = Icc 0 T :=
      Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx,ha _ hx.1⟩⟩
    rw [heq,Real.volume_real_Icc_of_le hT, sub_zero, one_mul]
  · rintro ⟨R,η,S,hR,hη,hh⟩
    by_contra hnot
    obtain ⟨T,hT,ha⟩ := c.exists_small_strip_occupation hflow hnot hR hη S
    exact ha.not_ge (hh T ((le_max_left S 1).trans hT.le))

end LengthGrowth.ActualFlow.ForwardImmersion
