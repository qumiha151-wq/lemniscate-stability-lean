import LengthGrowth.ActualFlow.CompactInflectionRate

noncomputable section
open Set Function
open scoped ContDiff
namespace LengthGrowth.ActualFlow.ForwardImmersion
open TurningEnvelope

private def admissible (γ : ℝ → ℂ) (x y : ℝ) : Prop :=
  curvature γ x = 0 ∧ curvatureGradient γ x ≤ 0 ∧
  curvature γ y = 0 ∧ 0 ≤ curvatureGradient γ y

private def outwardDifference (γ : ℝ → ℂ) (x y : ℝ) : ℝ :=
  arcDerivative γ (force γ) y - arcDerivative γ (force γ) x

private def physicalValues (c : ForwardImmersion) (t : ℝ) : Set ℝ :=
  insert 0 ((fun q : ℝ × ℝ => outwardDifference (c.position t) q.1 q.2) ''
    {q | admissible (c.position t) q.1 q.2})

/-- The nonnegative outward force-gradient rate, taking the supremum over
    all admissible material labels, including degenerate curvature zeros. -/
def physicalInflectionRate (c : ForwardImmersion) (t : ℝ) : ℝ := sSup (physicalValues c t)

private abbrev Labels (c : ForwardImmersion) := Icc (0:ℝ) c.period × Icc (0:ℝ) c.period
private abbrev Slab (c : ForwardImmersion) := Ioi (0:ℝ) × Labels c

private def graph (c : ForwardImmersion) : Set (Slab c) :=
  {q | admissible (c.position q.1) q.2.1 q.2.2}

private def difference (c : ForwardImmersion) (q : Slab c) : ℝ :=
  outwardDifference (c.position q.1) q.2.1 q.2.2

private def labelPoint {c : ForwardImmersion} (u : Slab c → ℝ) (q : Slab c) : ℝ × ℝ :=
  (q.1.val,u q)

private def curvatureField (c : ForwardImmersion) (z : ℝ × ℝ) := curvature (c.position z.1) z.2
private def gradientField (c : ForwardImmersion) (z : ℝ × ℝ) := curvatureGradient (c.position z.1) z.2
private def fluxField (c : ForwardImmersion) (z : ℝ × ℝ) :=
  arcDerivative (c.position z.1) (force (c.position z.1)) z.2

set_option maxHeartbeats 900000 in
private theorem jet_continuity (c : ForwardImmersion) (u : Slab c → ℝ) (hu : Continuous u) :
    Continuous (fun q : Slab c => curvature (c.position q.1) (u q)) ∧
    Continuous (fun q : Slab c => curvatureGradient (c.position q.1) (u q)) ∧
    Continuous (fun q : Slab c => arcDerivative (c.position q.1) (force (c.position q.1)) (u q)) := by
  have h : Continuous (labelPoint u) :=
    (continuous_subtype_val.comp continuous_fst).prodMk hu
  have mem (q : Slab c) : labelPoint u q ∈ Ioi (0:ℝ) ×ˢ (univ : Set ℝ) := ⟨q.1.2, mem_univ _⟩
  have k : ContinuousOn (curvatureField c)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := c.interior.curvature_joint_smooth.continuousOn
  have g : ContinuousOn (gradientField c)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := c.interior.curvatureGradient_joint_smooth.continuousOn
  have j : ContinuousOn (fluxField c)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := (c.interior.arcDerivative_joint_smooth
        (f := fun t => force (c.interior.position t)) c.interior.force_joint_smooth).continuousOn
  have ck : Continuous (curvatureField c ∘ labelPoint u) := k.comp_continuous h mem
  have cg : Continuous (gradientField c ∘ labelPoint u) := g.comp_continuous h mem
  have cj : Continuous (fluxField c ∘ labelPoint u) := j.comp_continuous h mem
  exact ⟨ck,cg,cj⟩

private theorem closed_data (c : ForwardImmersion) : IsClosed (graph c) ∧ Continuous (difference c) := by
  obtain ⟨kx, gx, jx⟩ := jet_continuity c (fun q => q.2.1.val)
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  obtain ⟨ky, gy, jy⟩ := jet_continuity c (fun q => q.2.2.val)
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  exact ⟨(isClosed_eq kx continuous_const).inter ((isClosed_le gx continuous_const).inter
    ((isClosed_eq ky continuous_const).inter (isClosed_le continuous_const gy))), jy.sub jx⟩

private theorem values_eq_compact (c : ForwardImmersion) (t : Ioi (0:ℝ)) :
    physicalValues c t = rateValues (graph c) (difference c) t := by
  apply congrArg (insert (0:ℝ))
  let γ := c.position t
  let tag := toIcoMod c.period_pos 0
  let rep := fun x : ℝ => (⟨tag x, Ico_subset_Icc_self (toIcoMod_mem_Ico' c.period_pos x)⟩ :
    Icc (0:ℝ) c.period)
  have wrap {f : ℝ → ℝ} (hf : Periodic f c.period) (x : ℝ) : f (rep x) = f x := by
    have h := hf.sub_zsmul_eq (x := x) (toIcoDiv c.period_pos 0 x)
    rwa [self_sub_toIcoDiv_zsmul] at h
  have smooth := c.position_slice_smooth t.2.le
  have regular := c.immersion t t.2.le
  have per := c.periodic t t.2.le
  have kp := curvature_periodic smooth regular per
  have gp := curvatureGradient_periodic smooth regular per
  have jp := arcDerivative_periodic smooth per ((force_smooth smooth regular).differentiable (by simp))
    (force_periodic smooth regular per)
  ext r
  constructor
  · rintro ⟨⟨x,y⟩,ok,eq⟩
    refine ⟨(rep x,rep y), ?_, ?_⟩
    · change curvature γ (rep x) = 0 ∧ curvatureGradient γ (rep x) ≤ 0 ∧
        curvature γ (rep y) = 0 ∧ 0 ≤ curvatureGradient γ (rep y)
      simpa only [γ, wrap kp, wrap gp] using
        (show curvature γ x = 0 ∧ curvatureGradient γ x ≤ 0 ∧ curvature γ y = 0 ∧ 0 ≤ curvatureGradient γ y from ok)
    · change arcDerivative γ (force γ) (rep y) - arcDerivative γ (force γ) (rep x) = r
      simpa only [γ, wrap jp] using (show arcDerivative γ (force γ) y - arcDerivative γ (force γ) x = r from eq)
  · rintro ⟨⟨x,y⟩,ok,eq⟩
    exact ⟨(x.val,y.val),ok,eq⟩

private theorem rate_eq_compact (c : ForwardImmersion) (t : Ioi (0:ℝ)) :
    c.physicalInflectionRate t = closedGraphRate (graph c) (difference c) t :=
  congrArg sSup (values_eq_compact c t)

theorem physicalInflectionRate_nonneg (c : ForwardImmersion) {t : ℝ} (ht : 0 < t) :
    0 ≤ c.physicalInflectionRate t := by
  rw [rate_eq_compact c ⟨t,ht⟩]
  exact closedGraphRate_nonneg (closed_data c).1 (closed_data c).2 _

theorem le_physicalInflectionRate (c : ForwardImmersion) {t : ℝ} (ht : 0 < t)
    (x y : ℝ) (kx : curvature (c.position t) x = 0) (gx : curvatureGradient (c.position t) x ≤ 0)
    (ky : curvature (c.position t) y = 0) (gy : 0 ≤ curvatureGradient (c.position t) y) :
    arcDerivative (c.position t) (force (c.position t)) y -
      arcDerivative (c.position t) (force (c.position t)) x ≤ c.physicalInflectionRate t := by
  let T : Ioi (0:ℝ) := ⟨t,ht⟩
  have mem : outwardDifference (c.position t) x y ∈
      (fun q : ℝ × ℝ => outwardDifference (c.position t) q.1 q.2) ''
        {q | admissible (c.position t) q.1 q.2} := ⟨(x,y), ⟨kx,gx,ky,gy⟩, rfl⟩
  have bounded : BddAbove (physicalValues c t) := by
    rw [values_eq_compact c T]
    exact (compact_rateValues (closed_data c).1 (closed_data c).2 T).bddAbove
  exact le_csSup bounded (mem_insert_of_mem _ mem)

theorem physicalInflectionRate_upperSemicontinuousOn (c : ForwardImmersion) :
    UpperSemicontinuousOn c.physicalInflectionRate (Ioi 0) := by
  apply upperSemicontinuousOn_iff_restrict.mp
  have eq : (Ioi (0:ℝ)).domRestrict c.physicalInflectionRate =
      closedGraphRate (graph c) (difference c) := funext (rate_eq_compact c)
  rw [eq]
  exact upperSemicontinuous_closedGraphRate (closed_data c).1 (closed_data c).2

theorem upperSemicontinuous_physicalInflectionRate_cut (c : ForwardImmersion) {a : ℝ} (ha : 0 < a) :
    UpperSemicontinuous (fun t => if a ≤ t then c.physicalInflectionRate t else 0) := by
  let clamp := fun t : ℝ => (⟨max a t, ha.trans_le (le_max_left ..)⟩ : Ioi (0:ℝ))
  have cc : Continuous clamp := (continuous_const.max continuous_id).subtype_mk _
  have rest : UpperSemicontinuous ((Ioi (0:ℝ)).domRestrict c.physicalInflectionRate) :=
    upperSemicontinuousOn_iff_restrict.mpr c.physicalInflectionRate_upperSemicontinuousOn
  have clipped := rest.comp cc
  change UpperSemicontinuous (fun t => c.physicalInflectionRate (max a t)) at clipped
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro b
  by_cases hb : b ≤ 0
  · convert isClosed_univ (X := ℝ) using 1
    ext t
    change (b ≤ if a ≤ t then c.physicalInflectionRate t else 0) ↔ t ∈ (univ : Set ℝ)
    by_cases ht : a ≤ t
    · simp [ht, hb.trans (c.physicalInflectionRate_nonneg (ha.trans_le ht))]
    · simp [ht, hb]
  · convert isClosed_Ici.inter (clipped.isClosed_preimage b) using 1
    ext t
    change (b ≤ if a ≤ t then c.physicalInflectionRate t else 0) ↔ a ≤ t ∧ b ≤ c.physicalInflectionRate (max a t)
    by_cases ht : a ≤ t
    · simp [ht]
    · simp [ht, hb]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.physicalInflectionRate_upperSemicontinuousOn
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.le_physicalInflectionRate
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.upperSemicontinuous_physicalInflectionRate_cut
