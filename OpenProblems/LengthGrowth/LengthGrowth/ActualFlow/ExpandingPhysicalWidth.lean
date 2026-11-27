import LengthGrowth.ActualFlow.UniformStraightening
import LengthGrowth.ActualFlow.StripCoercivity

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The strip direction and centre may depend on time. -/
def FitsPhysicalStrip (r t : ℝ) : Prop :=
  ∃ (z : ℂ) (h : ℝ), ‖z‖=1 ∧ ∀u, |(z*c.position t u).im-h|≤r

private theorem physical_strip_curvature {t r : ℝ} (ht : 0≤t) (hr : 0<r)
    (strip : c.FitsPhysicalStrip r t) : ∃u, 1≤(8*r)*|curvature (c.position t) u| := by
  obtain ⟨z,b,hz,fit⟩ := strip
  let p := c.regularPositionAt ht
  obtain ⟨s,hs⟩ := p.closedFrenetCurve.exists_curvature_in_strip hz hr (h:=b)
    (fun s => fit (p.arclengthInverse s))
  rw [p.closedFrenetCurve_curvature] at hs
  exact ⟨p.arclengthInverse s,hs⟩

theorem physical_strip_force_cost {t r : ℝ} (ht : 0≤t) (hr : 0<r) (fit : c.FitsPhysicalStrip r t) :
    1≤16777216*(8*r)^6*(c.energy t*c.dissipation t) := by
  obtain ⟨u,hu⟩ := c.physical_strip_curvature ht hr fit
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hu 6
  rw [one_pow,mul_pow] at h
  have p := (c.regularPositionAt ht).material_stress_coercivity u
  change 1/16777216*|curvature (c.position t) u|^6≤c.energy t*c.dissipation t at p
  nlinarith only [h,mul_le_mul_of_nonneg_left p (pow_nonneg (by positivity : 0≤8*r) 6)]

/-- In the original plane even the thinnest strip containing the entire curve
must widen without limit. Its centre and direction may be chosen anew at each time. -/
theorem eventually_outgrows_all_fixed_width_strips (flow : c.IsNormalFEF) {r : ℝ} (hr : 0<r) :
    ∀ᶠt in atTop, ¬c.FitsPhysicalStrip r t := by
  have p : 0<8*r := by positivity
  filter_upwards [c.uniform_curvature_and_gradient_decay flow (one_div_pos.mpr p),eventually_ge_atTop (0:ℝ)]
    with t cap ht
  intro fit
  obtain ⟨u,hu⟩ := c.physical_strip_curvature ht hr fit
  have h := (lt_div_iff₀ p).mp (cap u).1
  linarith only [h,hu]

/-- Every time block contains a slice on which *every* enclosing strip
pays the reciprocal sixth-power cost against the squared energy drop. -/
theorem exists_wide_slice_of_energy_drop (flow : c.IsNormalFEF) {s t : ℝ} (hs : 0<s) (st : s<t) :
    ∃u∈Icc s t, ∀r : ℝ, 0<r → c.FitsPhysicalStrip r u →
      2*(t-s)≤16777216*(8*r)^6*(c.energy s^2-c.energy t^2) := by
  let f := fun x => c.energy x*c.dissipation x
  have sub : Icc s t ⊆ Ici 0 := fun _ hx => hs.le.trans hx.1
  have cf : ContinuousOn f (Icc s t) := (c.energy_continuousOn.mono sub).mul (c.dissipation_continuousOn.mono sub)
  obtain ⟨u,hu,small⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr st.le) cf
  have ave := intervalIntegral.integral_mono_on (μ:=volume) st.le
    (intervalIntegrable_const (c:=f u)) (cf.intervalIntegrable_of_Icc st.le) (fun z hz => small hz)
  rw [intervalIntegral.integral_const,smul_eq_mul] at ave
  have der (x : ℝ) (hx : x∈Icc s t) : HasDerivAt (fun z => -(c.energy z)^2) (2*f x) x := by
    convert! (((c.energy_hasDerivAt_normal flow (hs.trans_le hx.1)).pow 2).neg) using 1
    dsimp [f]
    ring
  have exactDrop := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le st.le
    (fun x hx => (der x hx).continuousAt.continuousWithinAt)
    (fun x hx => der x ⟨hx.1.le,hx.2.le⟩) ((cf.const_mul 2).intervalIntegrable_of_Icc st.le)
  rw [intervalIntegral.integral_const_mul] at exactDrop
  refine ⟨u,hu,?_⟩
  intro r rp fit
  let A := 16777216*(8*r)^6
  have cost : 1≤A*f u := c.physical_strip_force_cost (sub hu) rp fit
  have loss : 2*((t-s)*f u)≤c.energy s^2-c.energy t^2 := by linarith only [ave,exactDrop]
  have pos : 0≤A := by dsimp [A]; positivity
  calc
    2*(t-s) = 2*(t-s)*1 := by ring
    _ ≤ 2*(t-s)*(A*f u) := mul_le_mul_of_nonneg_left cost (by linarith only [st])
    _ = A*(2*((t-s)*f u)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left loss pos

/-- On every sufficiently late doubling interval there is one slice whose
least containing width exceeds any prescribed multiple of time^(1/6).
The quantifiers are simultaneous across all possible strip directions. -/
theorem dyadic_width_exceeds_sixth_root (flow : c.IsNormalFEF) {A : ℝ} (ap : 0<A) :
    ∀ᶠs in atTop, ∃u∈Icc s (2*s), ¬c.FitsPhysicalStrip (A*u^(1/6:ℝ)) u := by
  let K := 16777216*(8*A)^6
  have kp : 0<K := by dsimp [K]; positivity
  let S := (fun t => c.energy t^2) '' Ici 1
  have ne : S.Nonempty := ⟨c.energy 1^2,1,mem_Ici.mpr le_rfl,rfl⟩
  have low : BddBelow S := ⟨0,by rintro _ ⟨x,_,rfl⟩; exact sq_nonneg _⟩
  obtain ⟨_,⟨v,hv,rfl⟩,near⟩ := exists_lt_of_csInf_lt ne
    (show sInf S<sInf S+1/K from lt_add_of_pos_right _ (one_div_pos.mpr kp))
  change 1≤v at hv
  filter_upwards [eventually_ge_atTop v] with s sv
  have sp : 0<s := by linarith
  have ss : s<2*s := by linarith
  obtain ⟨u,hu,wide⟩ := c.exists_wide_slice_of_energy_drop flow sp ss
  have up := sp.trans_le hu.1
  refine ⟨u,hu,?_⟩
  intro fit
  have eq : (8*(A*u^(1/6:ℝ)))^6=(8*A)^6*u := by
    rw [←mul_assoc,mul_pow,←Real.rpow_natCast (u^(1/6:ℝ)) 6,←Real.rpow_mul up.le]
    norm_num
  have g := wide _ (mul_pos ap (Real.rpow_pos_of_pos up _)) fit
  rw [eq] at g
  have e := pow_le_pow_left₀ (c.energy_nonneg s) (c.energy_le_of_le flow (by linarith : 0≤v) sv) 2
  have infimum := csInf_le low (show c.energy (2*s)^2∈S from ⟨2*s,by change 1≤2*s; linarith,rfl⟩)
  let loss := c.energy s^2-c.energy (2*s)^2
  have err : loss<1/K := by dsimp [loss]; linarith only [near,e,infimum]
  have key : K*loss<1 := by simpa only [mul_comm K] using (lt_div_iff₀ kp).mp err
  have imposs := mul_lt_mul_of_pos_left key up
  have cap : 2*(2*s-s)≤u*(K*loss) := by
    dsimp [K,loss]
    linarith only [g]
  linarith only [cap,imposs,hu.2]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.eventually_outgrows_all_fixed_width_strips
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.exists_wide_slice_of_energy_drop
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.dyadic_width_exceeds_sixth_root
