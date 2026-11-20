import SolitonClassification.MovingSeamCrossing

noncomputable section
open Set Metric Filter
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam

theorem uniform_height_lipschitz {a b D S T : ℝ} (hS : 0≤S) (st : S≤T)
    (safe : ∀x : Icc a b × Icc (0:ℝ) D, ∀t∈Icc S T, regular (shot x.2 x.1 t)) :
    ∃ K≥0, ∀ (c : Icc a b) (d e : Icc (0:ℝ) D) (t : ℝ), t∈Icc S T →
      |height (shot d c t)-height (shot e c t)| ≤ K*|(d:ℝ)-e| := by
  let X := (Icc a b) × (Icc (0:ℝ) D)
  let f := fun w : X × (Icc S T) => shot w.1.2 w.1.1 w.2
  have cf : Continuous f := continuous_shot (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)) (continuous_subtype_val.comp continuous_snd)
  have localLip : LocallyLipschitzOn (range f) height := by
    rintro _ ⟨w,rfl⟩
    obtain ⟨K,U,hU,hL⟩ := (height_smooth (safe w.1 w.2 w.2.property)).exists_lipschitzOnWith
    exact ⟨K,U,mem_nhdsWithin_of_mem_nhds hU,hL⟩
  obtain ⟨K,hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (isCompact_range cf) localLip
  let dat : X → Data := fun x => ((x.2:ℝ),![(x.1:ℝ),0,1,0])
  have cd : Continuous dat := by
    apply (continuous_subtype_val.comp continuous_snd).prodMk
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  obtain ⟨C,hC,est⟩ := compact_initial_estimate (isCompact_range cd) (hS.trans st)
  refine ⟨K*C,mul_nonneg K.coe_nonneg hC.le,?_⟩
  intro c d e t ht
  let x : X := (c,d)
  let y : X := (c,e)
  let tt : Icc S T := ⟨t,ht⟩
  have bound := est _ (mem_range_self x) _ (mem_range_self y) t
    (by rw [abs_of_nonneg (hS.trans ht.1)]; exact ht.2)
  have dd : dist (dat x) (dat y)=|(d:ℝ)-e| := by
    change max (dist (d:ℝ) e) (dist (![c,0,1,0] : Phase) ![c,0,1,0]) = _
    rw [dist_self,max_eq_left dist_nonneg,Real.dist_eq]
  rw [dd] at bound
  have contraction : dist (f (x,tt)) (f (y,tt)) ≤ dist (extended (dat x) t) (extended (dat y) t) :=
    le_max_right .. 
  have bnd : dist (f (x,tt)) (f (y,tt)) ≤ C*|(d:ℝ)-e| := contraction.trans bound
  calc
    _ = dist (height (f (x,tt))) (height (f (y,tt))) := by rw [Real.dist_eq]
    _ ≤ K*dist (f (x,tt)) (f (y,tt)) :=
      hK.dist_le_mul _ (mem_range_self (x,tt)) _ (mem_range_self (y,tt))
    _ ≤ K*(C*|(d:ℝ)-e|) := mul_le_mul_of_nonneg_left bnd K.coe_nonneg
    _ = _ := by ring

/-- Lipschitz dependence in the seam scale d, uniform in the initial curvature
    and joint continuity in both shooting parameters on the same physical slab. -/
theorem moving_seam_time (a b : ℝ) :
    ∃S≥20, ∃H₀, ∀H≥H₀, ∃T>S, ∃D>0, ∃K≥0, ∃τ : Icc a b × Icc (0:ℝ) D → ℝ,
      Continuous τ ∧ (∀x, τ x∈Ioo S T ∧ height (shot x.2 x.1 (τ x))=H ∧
        ∀t∈Icc S T,height (shot x.2 x.1 t)=H → t=τ x) ∧
      (∀(c : Icc a b) (d e : Icc (0:ℝ) D), |τ (c,d)-τ (c,e)| ≤ K*|(d:ℝ)-e|) ∧
      ∀x : Icc a b × Icc (0:ℝ) D, ∀t∈Icc S T,
        regular (shot x.2 x.1 t) ∧ 1/8<heightRate (x.2,shot x.2 x.1 t) := by
  obtain ⟨S,hS,H₀,w⟩ := continuous_moving_seam_crossing a b
  refine ⟨S,hS,H₀,?_⟩
  intro H hH
  obtain ⟨T,st,D,hD,τ,cτ,hit,compare,safe⟩ := w H hH
  obtain ⟨K,hK,lip⟩ := uniform_height_lipschitz (by linarith : 0≤S) st.le
    (fun x t ht => (safe x t ht).1)
  refine ⟨T,st,D,hD,8*K,by positivity,τ,cτ,hit,?_,safe⟩
  intro c d e
  have l := lip c d e _ (Ioo_subset_Icc_self (hit (c,e)).1)
  calc
    _ ≤ _ := compare (c,d) (c,e)
    _ ≤ 8*(K*|(d:ℝ)-e|) := mul_le_mul_of_nonneg_left l (by norm_num)
    _ = _ := by ring

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.moving_seam_time
