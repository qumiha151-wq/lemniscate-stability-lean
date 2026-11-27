import LengthGrowth.ActualFlow.NodalSquare
import Mathlib.MeasureTheory.Function.JacobianOneDim

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace LengthGrowth.ActualFlow

/-- All times above H at which no earlier time after T had a greater value. -/
def highRecordSet (f : ℝ→ℝ) (T H : ℝ) :=
  {s | T≤s ∧ H<f s ∧ ∀u,T≤u → u≤s → f u≤f s}

private theorem measurable_highRecordSet {f : ℝ→ℝ} {T H : ℝ} (hf : Continuous f) :
    MeasurableSet (highRecordSet f T H) := by
  let B := ⋂ u : Ici T, (Iic (u:ℝ) ∪ f ⁻¹' Ici (f u))
  have hb : IsClosed B := isClosed_iInter fun u=>isClosed_Iic.union (isClosed_Ici.preimage hf)
  have eq : highRecordSet f T H=(Ici T ∩ f ⁻¹' Ioi H) ∩ B := by
    ext s
    constructor
    · rintro ⟨ts,hs,h⟩
      refine ⟨⟨ts,hs⟩,mem_iInter.mpr (fun u=>?_ )⟩
      by_cases us : (u:ℝ)≤s
      · exact Or.inr (h _ u.2 us)
      · exact Or.inl (le_of_not_ge us)
    · rintro ⟨⟨ts,hs⟩,h⟩
      refine ⟨ts,hs,fun u tu us => ?_⟩
      rcases mem_iInter.mp h (⟨u,tu⟩ : Ici T) with su|le
      · exact le_of_eq (congrArg f (le_antisymm us su))
      · exact le
  rw [eq]; exact (measurableSet_Ici.inter (hf.measurable measurableSet_Ioi)).inter hb.measurableSet

private theorem record_image {f : ℝ→ℝ} {T H t : ℝ} (hf : Continuous f) (start : f T≤H)
    (tt : T≤t) : Ioc H (f t) ⊆ f '' highRecordSet f T H := by
  intro y hy
  obtain ⟨x,hx,eq⟩ := intermediate_value_Icc tt hf.continuousOn (show y∈Icc (f T) (f t) from
    ⟨start.trans hy.1.le,hy.2⟩)
  let C := (Icc T t) ∩ f ⁻¹' ({y} : Set ℝ)
  have cc : IsCompact C := isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  obtain ⟨s,hs,lo⟩ := cc.exists_isMinOn (show C.Nonempty from ⟨x,hx,eq⟩) continuous_id.continuousOn
  have eqs : f s=y := hs.2
  refine ⟨s,⟨hs.1.1,eqs ▸ hy.1,?_⟩,eqs⟩
  intro u tu us
  by_contra! bad
  obtain ⟨z,hz,ez⟩ := intermediate_value_Icc tu hf.continuousOn
    (show y∈Icc (f T) (f u) from ⟨start.trans hy.1.le,eqs ▸ bad.le⟩)
  have sz : s≤z := lo (show z∈C from ⟨⟨hz.1,(hz.2.trans us).trans hs.1.2⟩,ez⟩)
  have zu : z=u := le_antisymm hz.2 (us.trans sz)
  exact bad.ne (eqs.trans ((zu ▸ ez).symm))

/-- Only the allowance on increasing high records is integrated. At every
other time, including all constant records, its contribution is zero. -/
theorem bound_of_positive_record_budget {f v G : ℝ→ℝ} {T H K : ℝ}
    (hf : Continuous f) (hT : f T≤H) (kn : 0≤K)
    (hd : ∀s,T<s → HasDerivAt f (v s) s) (dom : ∀s,T<s → v s≤G s)
    (budget : (∫⁻s in highRecordSet f T H, if 0<v s then ENNReal.ofReal (G s) else 0)
      ≤ ENNReal.ofReal K) : ∀t,T≤t → f t≤H+K := by
  intro t tt
  have hm : MeasurableSet (highRecordSet f T H) := measurable_highRecordSet hf
  have late (s : ℝ) (h : s∈highRecordSet f T H) : T<s := lt_of_le_of_ne h.1 (fun e=> by
    have := h.2.1; rw [←e] at this; linarith only [hT,this])
  have mono : MonotoneOn f (highRecordSet f T H) := fun s hs t ht st=> ht.2.2 s hs.1 st
  have area := lintegral_deriv_eq_volume_image_of_monotoneOn hm
    (fun s hs=>(hd s (late s hs)).hasDerivWithinAt) mono
  have comp : (∫⁻s in highRecordSet f T H, ENNReal.ofReal (v s))≤
      ∫⁻s in highRecordSet f T H, if 0<v s then ENNReal.ofReal (G s) else 0 := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ:=volume) hm] with s hs
    by_cases pos : 0<v s
    · simpa only [if_pos pos] using ENNReal.ofReal_le_ofReal (dom s (late s hs))
    · simp [pos,ENNReal.ofReal_of_nonpos (le_of_not_gt pos)]
  have out := (measure_mono (μ:=volume) (record_image hf hT tt)).trans (area ▸ comp.trans budget)
  rw [Real.volume_Ioc] at out
  have := (ENNReal.ofReal_le_ofReal_iff kn).mp out
  linarith

namespace ForwardImmersion
variable (c : ForwardImmersion)
def tailProduct (T t : ℝ) := c.normalizedProduct (max T t)
def productRate (t : ℝ) := c.energy t*c.lengthRate t-c.length t*c.dissipation t

theorem quarter_bounds_of_high_record_nodal_budget (hf : c.IsNormalFEF) {T H K : ℝ}
    (tp : 0<T) (hH : c.normalizedProduct T≤H) (kn : 0≤K)
    (budget : (∫⁻s in highRecordSet (c.tailProduct T) T H,
      if 0<c.productRate s then ENNReal.ofReal (c.nodalSquareAllowance s) else 0)≤ENNReal.ofReal K) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound := by
  have cg : Continuous (c.tailProduct T) := c.normalizedProduct_continuousOn.comp_continuous
    (continuous_const.max continuous_id) (fun x=>tp.le.trans (le_max_left ..))
  have same (s : ℝ) (h : T<s) : c.tailProduct T =ᶠ[nhds s] c.normalizedProduct := by
    filter_upwards [lt_mem_nhds h] with x hx
    simp [tailProduct,max_eq_right hx.le]
  have dt (s : ℝ) (h : T<s) := (c.normalizedProduct_hasDerivAt_normal hf (tp.trans h)).congr_of_eventuallyEq (same s h)
  have ge : c.tailProduct T T≤H := by simpa [tailProduct] using hH
  have result := bound_of_positive_record_budget cg ge kn dt (fun s hs=> by
    have a := c.deriv_product_le_nodalSquareAllowance hf (tp.trans hs)
    rwa [(c.normalizedProduct_hasDerivAt_normal hf (tp.trans hs)).deriv] at a) budget
  obtain ⟨q,_,best⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr tp.le)
    (c.normalizedProduct_continuousOn.mono (fun _ h=>h.1))
  have bounded : c.HasBoundedEnergyLength := by
    refine ⟨max (c.normalizedProduct q) (H+K),fun t ht=>?_⟩
    change c.normalizedProduct t≤_
    by_cases before : t≤T
    · exact (best ⟨ht,before⟩).trans (le_max_left ..)
    · have st : T≤t := le_of_not_ge before
      exact (show c.normalizedProduct t≤H+K by simpa [tailProduct,max_eq_right st] using result t st).trans (le_max_right ..)
  have L := (c.quarter_length_iff_bounded_energyLength hf).mpr bounded
  exact ⟨L,c.quarter_energy_of_quarter_length hf L⟩
/-- For any fixed positive initial time, no threshold with a finite
increasing-record slope budget exists exactly when fourth-root growth fails. -/
theorem quarter_length_iff_high_record_nodal_budget (hf : c.IsNormalFEF) {T : ℝ} (tp : 0<T) :
    c.HasQuarterLengthBound ↔ ∃ H K : ℝ, c.normalizedProduct T≤H ∧ 0≤K ∧
      (∫⁻s in highRecordSet (c.tailProduct T) T H,
        if 0<c.productRate s then ENNReal.ofReal (c.nodalSquareAllowance s) else 0)≤ENNReal.ofReal K := by
  constructor
  · intro bounded
    obtain ⟨H,cap⟩ := (c.quarter_length_iff_bounded_energyLength hf).mp bounded
    refine ⟨H,0,cap T tp.le,le_rfl,?_⟩
    have empty : highRecordSet (c.tailProduct T) T H=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro s hs
      have h := cap (max T s) (tp.le.trans (le_max_left ..))
      exact (not_lt_of_ge h) hs.2.1
    simp [empty]
  · rintro ⟨H,K,less,kn,integral⟩
    exact (c.quarter_bounds_of_high_record_nodal_budget hf tp less kn integral).1
end ForwardImmersion
end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_bounds_of_high_record_nodal_budget
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_iff_high_record_nodal_budget
