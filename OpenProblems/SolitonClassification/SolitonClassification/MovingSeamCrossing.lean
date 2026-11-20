import SolitonClassification.MovingSeamSlab
import SolitonClassification.TransverseTime

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open FrozenStress

private theorem uniform_radial (a b R : ℝ) :
    ∃T≥0, ∀ c∈Icc a b, ∀t≥T, R < -(seam c).radial t := by
  let Z := fun c : Icc a b => seam c
  have cs (i : Fin 4) (t : ℝ) : Continuous (fun c : Icc a b => coords (Z c) t i) :=
    (continuous_apply i).comp (continuous_seam_coordinates.comp (continuous_const.prodMk continuous_subtype_val))
  obtain ⟨T,hT,w⟩ := uniform_seam_entrance Z (fun c => by
    obtain ⟨_,hv,_,hq⟩ := seam_initial c
    simp [Z,Orbit.radial,hv,hq]) (fun c => (seam_initial c).2.2.1)
    (fun t => ((((cs 0 t).pow 2).div_const 2).mul (cs 3 t)).add ((cs 1 t).mul (cs 2 t))) R
  exact ⟨T,hT,fun c hc => w ⟨c,hc⟩⟩

/-- At every sufficiently high prescribed corrected radial level one common
    finite time slab persists for a whole strip of nonzero physical scales.
    The true polynomial seam shots have unique crossings on this slab. -/
theorem continuous_moving_seam_crossing (a b : ℝ) :
    ∃S≥20, ∃H₀, ∀H≥H₀, ∃T>S, ∃D>0, ∃τ : Icc a b × Icc (0:ℝ) D → ℝ,
      Continuous τ ∧ (∀x, τ x∈Ioo S T ∧ height (shot x.2 x.1 (τ x))=H ∧
        ∀t∈Icc S T,height (shot x.2 x.1 t)=H → t=τ x) ∧
      (∀x y, |τ x-τ y| ≤ 8*|height (shot x.2 x.1 (τ y))-height (shot y.2 y.1 (τ y))|) ∧
      ∀x : Icc a b × Icc (0:ℝ) D, ∀t∈Icc S T,
        regular (shot x.2 x.1 t) ∧ 1/8<heightRate (x.2,shot x.2 x.1 t) := by
  obtain ⟨S',_,enter⟩ := uniform_radial a b 12
  let S := max 20 S'
  have r (c : ℝ) (hc : c∈Icc a b) (t : ℝ) (ht : S≤t) : 12< -(seam c).radial t :=
    enter c hc t ((le_max_right ..).trans ht)
  have A (c : ℝ) (hc : c∈Icc a b) (t : ℝ) (ht : S≤t) : 12≤(seam c).amplitude t := by
    have p := (seam c).stress_unit t
    have nn : 0≤(seam c).amplitude t := Real.sqrt_nonneg _
    nlinarith [sq_nonneg ((seam c).transverse t),r c hc t ht]
  let F := fun c : Icc a b => shot 0 c S
  have cf : Continuous F := continuous_shot continuous_const continuous_subtype_val continuous_const
  have hf : Continuous (fun c : Icc a b => height (F c)) := by
    apply continuous_iff_continuousAt.mpr
    intro c
    have reg : regular (F c) := by
      rw [show F c= coords (seam c) S from shot_frozen ..]
      exact frozen_regular _ _ (by linarith [A _ c.property _ le_rfl])
    exact (height_smooth reg).continuousAt.comp cf.continuousAt
  obtain ⟨L,upper⟩ := (isCompact_range hf).bddAbove
  refine ⟨S,le_max_left ..,L+1,?_⟩
  intro H hH
  obtain ⟨T',_,large⟩ := uniform_radial a b (H+2)
  let T := max (S+1) T'
  have st : S<T := lt_of_lt_of_le (by linarith) (le_max_left (S+1) T')
  have lp (c : ℝ) (hc : c∈Icc a b) : (seam c).outgoingHeight S < H := by
    have w := upper (mem_range_self (⟨c,hc⟩ : Icc a b))
    change height (shot 0 c S) ≤ L at w
    rw [shot_frozen,frozen_height] at w
    linarith
  have rp (c : ℝ) (hc : c∈Icc a b) : H < (seam c).outgoingHeight T := by
    linarith [(abs_le.mp ((seam c).large_amplitude_height (A _ hc T st.le)).1).1,
      large c hc T (le_max_right ..)]
  have l := strict_endpoint (fun c hc => by linarith [A c hc S le_rfl]) (fun x => x<H) isOpen_Iio lp
  have r' := strict_endpoint (fun c hc => by linarith [A c hc T st.le]) (fun x => H<x) isOpen_Ioi rp
  have rate := rate_tube a b S T (fun c hc t ht => A c hc t ht.1)
  obtain ⟨ε,ep,all⟩ := Metric.mem_nhds_iff.mp ((l.and r').and rate)
  let D := ε/2
  have Dp : 0<D := by dsimp [D]; positivity
  let X := Icc a b × Icc (0:ℝ) D
  have ball (x : X) : (x.2:ℝ)∈Metric.ball (0:ℝ) ε := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg x.2.property.1]
    exact x.2.property.2.trans_lt (half_lt_self ep)
  have data (x : X) := all (ball x)
  let f := fun (x : X) (t : ℝ) => height (shot x.2 x.1 t)
  have cc (t : ℝ) (ht : t∈Icc S T) : Continuous (fun x => f x t) := by
    have sub : Continuous (fun x : X => shot x.2 x.1 t) := continuous_shot
      (continuous_subtype_val.comp continuous_snd) (continuous_subtype_val.comp continuous_fst) continuous_const
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ContinuousAt.comp (f:=fun y : X => shot y.2 y.1 t) (x:=x)
      (height_smooth ((data x).2 x.1 x.1.property t ht).1).continuousAt sub.continuousAt
  obtain ⟨τ,cτ,hit,lip⟩ := transverse_time f st cc (fun x t ht => by
    obtain ⟨reg,speed⟩ := (data x).2 x.1 x.1.property t ht
    have hd := rate_eq (x.2:ℝ) ![(x.1:ℝ),0,1,0] t reg
    exact ⟨hd.differentiableAt,speed.le.trans_eq hd.deriv.symm⟩)
    (fun x => (data x).1.1 x.1 x.1.property) (fun x => (data x).1.2 x.1 x.1.property)
  exact ⟨T,st,D,Dp,τ,cτ,hit,lip,fun x => (data x).2 _ x.1.property⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.continuous_moving_seam_crossing
