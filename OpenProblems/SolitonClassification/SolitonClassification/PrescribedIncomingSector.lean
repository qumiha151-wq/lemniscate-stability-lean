import SolitonClassification.PrescribedSeamSections

noncomputable section
open Set Filter Metric
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open FrozenStress

def sector (z : Phase) := 0<along z ∧ 4<root z/scale z

lemma sector_open_at {z : Phase} (h : regular z) (s : sector z) :
    ∀ᶠ x in 𝓝 z, sector x := by
  have as : 0 < amplitude z := Real.sqrt_pos.mpr h.2
  have cs : ContinuousAt scale z := by
    apply ContinuousAt.rpow_const _ (Or.inl h.1.ne'); unfold radiusSquared; fun_prop
  have ca : ContinuousAt amplitude z := by unfold amplitude stressSquared; fun_prop
  have cr : ContinuousAt root z := ca.sqrt
  have sp : 0<scale z := Real.rpow_pos_of_pos h.1 _
  have cal : ContinuousAt along z := by
    apply ContinuousAt.div _ (ca.mul (cs.pow 3)) (mul_ne_zero as.ne' (pow_ne_zero _ sp.ne')); fun_prop
  exact (cal.tendsto.eventually (eventually_gt_nhds s.1)).and
    ((cr.div cs sp.ne').tendsto.eventually (eventually_gt_nhds s.2))

/-- The frozen incoming side eventually has positive radial alignment and
    normalized root greater than four, uniformly on any compact curvature
    interval. The criterion only uses the corrected height and a time ≥20. -/
theorem frozen_sector_at_high_level (a b : ℝ) :
    ∃ B : ℝ, ∀c∈Icc a b, ∀t≥20, B≤(seam c).outgoingHeight t → sector (shot 0 c (-t)) := by
  let Z := fun c : Icc a b => seam c
  have cs (i : Fin 4) (t : ℝ) : Continuous (fun c : Icc a b => coords (Z c) t i) :=
    (continuous_apply i).comp (continuous_seam_coordinates.comp (continuous_const.prodMk continuous_subtype_val))
  obtain ⟨T,_,escape⟩ := uniform_seam_entrance Z (fun c => by
    obtain ⟨_,hv,_,hq⟩ := seam_initial c
    simp [Z,Orbit.radial,hv,hq]) (fun c => (seam_initial c).2.2.1)
    (fun t => ((((cs 0 t).pow 2).div_const 2).mul (cs 3 t)).add ((cs 1 t).mul (cs 2 t))) 32
  let X := Icc a b × Icc (20:ℝ) T
  let f := fun x : X => shot 0 x.1 x.2
  have co : Continuous f := continuous_shot continuous_const (continuous_subtype_val.comp continuous_fst)
    (continuous_subtype_val.comp continuous_snd)
  have ch : Continuous (fun x : X => height (f x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have pos : 0<(x.2:ℝ) := by linarith [x.2.property.1]
    have rad := seam_radial_strict x.1 pos
    have amp : 0<(seam x.1).amplitude x.2 := by
      have h := (seam x.1).stress_unit x.2
      nlinarith [sq_nonneg ((seam x.1).transverse x.2),Real.sqrt_nonneg (stressSquared (coords (seam x.1) x.2)),sq_pos_of_neg rad,
        show 0≤(seam x.1).amplitude x.2 from Real.sqrt_nonneg _]
    have rg : regular (f x) := by
      change regular (shot 0 x.1 x.2)
      rw [shot_frozen]; exact frozen_regular _ _ amp
    exact ContinuousAt.comp (f:=f) (height_smooth rg).continuousAt co.continuousAt
  obtain ⟨L,bound⟩ := (isCompact_range ch).bddAbove
  refine ⟨L+1,?_⟩
  intro c hc t ht high
  have late : T≤t := by
    by_contra! e
    have u := bound (mem_range_self ((⟨c,hc⟩,⟨t,ht,e.le⟩) : X))
    change height (shot 0 c t)≤L at u
    rw [shot_frozen,frozen_height] at u
    linarith
  obtain ⟨_,v,_,q⟩ := seam_initial c
  have p := (seam c).seam_impact_radial_parity v q t |>.2
  have far := escape (⟨c,hc⟩ : Icc a b) t late
  change 32 < -(seam c).radial t at far
  have rr : 32<(seam c).radial (-t) := by linarith
  have aa : 32<(seam c).amplitude (-t) := by
    have bd := (seam c).stress_unit (-t)
    nlinarith [sq_nonneg ((seam c).transverse (-t)),show 0≤(seam c).amplitude (-t) from Real.sqrt_nonneg _]
  let x := coords (seam c) (-t)
  have hs : scale x=1 := by simp [x,scale,radiusSquared,coords,(seam c).unit (-t)]
  have root4 : 4<(seam c).root (-t) := by
    apply (Real.lt_sqrt (by norm_num : (0:ℝ)≤4)).mpr
    linarith
  rw [shot_frozen]
  change 0<along x ∧ 4<root x/scale x
  rw [along,hs,one_pow,mul_one,div_one]
  exact ⟨div_pos (by change 0<(seam c).radial (-t);linarith) (by change 0<(seam c).amplitude (-t);linarith),root4⟩

/-- All the prescribed small positive radii remain in the incoming chart.
    A common bound holds for every seam curvature in the compact family. -/
theorem prescribed_sector_strip (a b : ℝ) :
    ∃ B : ℝ, ∀ H≥B, ∀ E>0, ∀ w : PrescribedSection a b H E,
      ∃ D∈Ioc 0 E, ∀ z : Icc a b × Icc (0:ℝ) E, (z.2:ℝ)≤D →
        sector (shot (w.drive z) z.1 (-w.flight z)) := by
  obtain ⟨B,frozen⟩ := frozen_sector_at_high_level a b
  refine ⟨B,?_⟩
  intro H hH E ep w
  let O : Icc (0:ℝ) E := ⟨0,le_rfl,ep.le⟩
  let F := fun z : Icc a b × Icc (0:ℝ) E => shot (w.drive z) z.1 (-w.flight z)
  have cf : Continuous F := continuous_shot w.continuous_drive (continuous_subtype_val.comp continuous_fst) w.continuous_flight.neg
  have sec (c : Icc a b) : sector (F (c,O)) := by
    have zero := w.frozen (c,O) rfl
    have h := w.incoming (c,O)
    rw [zero,shot_reflection,(reflected_data _).1,neg_neg,shot_frozen,frozen_height] at h
    dsimp only [F]; rw [zero]
    exact frozen c c.property _ (w.late (c,O)).le (hH.trans_eq h.symm)
  have nb (c : Icc a b) : ∀ᶠ z in 𝓝 ((c,O) : Icc a b × Icc (0:ℝ) E), sector (F z) :=
    (cf.tendsto _).eventually (sector_open_at (w.regular_incoming (c,O)) (sec c))
  have hmem := isCompact_univ.mem_nhdsSet_prod_of_forall (s:={z | sector (F z)}) (l:=𝓝 O)
    (fun c _ => by rw [←nhds_prod_eq]; exact nb c)
  obtain ⟨u,hu,v,hv,good⟩ := Filter.mem_prod_iff.mp hmem
  obtain ⟨δ,hδ,inV⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨min E (δ/2),⟨lt_min ep (by positivity),min_le_left ..⟩,?_⟩
  intro z hz
  apply good
  refine ⟨(subset_of_mem_nhdsSet hu) (mem_univ _),inV ?_⟩
  change |(z.2:ℝ)-0|<δ
  rw [sub_zero,abs_of_nonneg z.2.property.1]
  exact (hz.trans (min_le_right ..)).trans_lt (half_lt_self hδ)

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.prescribed_sector_strip
