import SolitonClassification.MovingSeamHeight

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set Filter FrozenStress
open scoped Topology

def shot (d c t : ℝ) := solution d ![c,0,1,0] t
theorem shot_frozen (c t : ℝ) : shot 0 c t = coords (seam c) t :=
  congrFun (seam_solution c).symm t

lemma continuous_shot {X : Type*} [TopologicalSpace X] {d c t : X→ℝ}
    (hd : Continuous d) (hc : Continuous c) (ht : Continuous t) :
    Continuous (fun x => shot (d x) (c x) (t x)) := by
  have cvec : Continuous (fun x => (![c x,0,1,0] : Phase)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact continuous_solution.comp (ht.prodMk (hd.prodMk cvec))

/-- One scale neighborhood works simultaneously for a compact family. -/
lemma tube {X : Type*} [TopologicalSpace X] [CompactSpace X] {P : X×ℝ → Prop}
    (h : ∀x, ∀ᶠ y in 𝓝 (x,(0:ℝ)), P y) :
    ∀ᶠ d in 𝓝 (0:ℝ), ∀x, P (x,d) := by
  have mem := isCompact_univ.mem_nhdsSet_prod_of_forall (s:={y | P y}) (l:=𝓝 (0:ℝ))
    (fun x _ => by rw [←nhds_prod_eq]; exact h x)
  obtain ⟨u,hu,v,hv,sub⟩ := Filter.mem_prod_iff.mp mem
  exact Filter.mem_of_superset hv fun d hd x => sub ⟨(subset_of_mem_nhdsSet hu) (mem_univ x),hd⟩

/-- Uniform positive speed is inherited by a whole time slab of perturbed
    normalized seam trajectories. The bound is taken in the constant clock. -/
theorem rate_tube (a b S T : ℝ)
    (hA : ∀ c∈Icc a b, ∀ t∈Icc S T, 12≤(seam c).amplitude t) :
    ∀ᶠ d in 𝓝 (0:ℝ), ∀ c∈Icc a b, ∀ t∈Icc S T,
      regular (shot d c t) ∧ 1/8 < heightRate (d,shot d c t) := by
  let X := (Icc a b) × (Icc S T)
  let F := fun y : X × ℝ => shot y.2 y.1.1 y.1.2
  have cf : Continuous F := continuous_shot continuous_snd
    (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
    (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
  have each (x : X) : ∀ᶠ y in 𝓝 (x,(0:ℝ)), regular (F y) ∧ 1/8<heightRate (y.2,F y) := by
    have ap := hA _ x.1.property _ x.2.property
    have reg : regular (F (x,0)) := by
      change regular (shot 0 x.1 x.2)
      rw [shot_frozen]
      exact frozen_regular _ _ (by linarith)
    have good : ∀ᶠ y in 𝓝 (x,(0:ℝ)), regular (F y) := cf.continuousAt (regular_open.mem_nhds reg)
    have rate : (1:ℝ)/8 < heightRate (0,F (x,0)) := by
      change (1:ℝ)/8 < heightRate (0,shot 0 x.1 x.2)
      rw [shot_frozen,frozen_rate _ _ (by linarith)]
      linarith [((seam x.1).large_amplitude_height ap).2]
    have lim := (rate_continuousAt reg).comp (continuous_snd.prodMk cf).continuousAt
    exact good.and (lim.tendsto.eventually (eventually_gt_nhds rate))
  filter_upwards [tube each] with d hd
  exact fun c hc t ht => hd (⟨c,hc⟩,⟨t,ht⟩)

lemma strict_endpoint {a b t : ℝ} (ap : ∀c∈Icc a b, 0<(seam c).amplitude t)
    (P : ℝ → Prop) (op : IsOpen {x | P x})
    (test : ∀c∈Icc a b, P ((seam c).outgoingHeight t)) :
    ∀ᶠ d in 𝓝 (0:ℝ), ∀ c∈Icc a b, P (height (shot d c t)) := by
  let F := fun y : (Icc a b) × ℝ => shot y.2 y.1 t
  have cf : Continuous F := continuous_shot continuous_snd (continuous_subtype_val.comp continuous_fst) continuous_const
  have e (c : Icc a b) : ∀ᶠ y in 𝓝 (c,(0:ℝ)), P (height (F y)) := by
    have fr : F (c,0) = coords (seam c) t := shot_frozen _ _
    have good := frozen_regular c t (ap c c.property)
    have lim : ContinuousAt (fun y => height (F y)) (c,0) :=
      ((height_smooth (fr ▸ good)).continuousAt.comp cf.continuousAt)
    apply lim.tendsto
    apply op.mem_nhds
    change P (height (F (c,0)))
    rw [fr,frozen_height]
    exact test c c.property
  filter_upwards [tube e] with d hd
  exact fun c hc => hd ⟨c,hc⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.rate_tube
