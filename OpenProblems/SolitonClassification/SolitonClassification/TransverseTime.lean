import SolitonClassification.FrozenSectionMap

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam

/-- Unique continuous crossing on a common time interval. The quantitative
    dependence estimate compares parameters at the same time and thus allows
    a uniform Lipschitz estimate for the flow to pass to the time selector. -/
theorem transverse_time {X : Type*} [TopologicalSpace X] (F : X → ℝ → ℝ) {S T H : ℝ}
    (st : S<T) (hc : ∀t∈Icc S T,Continuous (fun x => F x t))
    (df : ∀x t,t∈Icc S T → DifferentiableAt ℝ (F x) t ∧ 1/8≤deriv (F x) t)
    (left : ∀x,F x S<H) (right : ∀x,H<F x T) :
    ∃ τ : X → ℝ, Continuous τ ∧ (∀x, τ x∈Ioo S T ∧ F x (τ x)=H ∧
      ∀t∈Icc S T,F x t=H → t=τ x) ∧
      ∀x y, |τ x-τ y|≤8*|F x (τ y)-F y (τ y)| := by
  have metric (x : X) (u v : ℝ) (hu : u∈Icc S T) (hv : v∈Icc S T) :
      |u-v|≤8*|F x u-F x v| := by
    have inc (s t : ℝ) (hs : s∈Icc S T) (ht : t∈Icc S T) (lt : s<t) :
        t-s≤8*(F x t-F x s) := by
      have inside : Icc s t ⊆ Icc S T := Icc_subset_Icc hs.1 ht.2
      obtain ⟨w,hw,rate⟩ := exists_deriv_eq_slope (F x) lt
        (fun _ h => (df x _ (inside h)).1.continuousAt.continuousWithinAt)
        (fun _ h => (df x _ (inside ⟨h.1.le,h.2.le⟩)).1.differentiableWithinAt)
      have lo := (le_div_iff₀ (sub_pos.mpr lt)).mp
        ((df x _ (inside ⟨hw.1.le,hw.2.le⟩)).2.trans_eq rate)
      linarith
    rcases lt_trichotomy u v with h|h|h
    · rw [abs_of_nonpos (sub_nonpos.mpr h.le)]
      linarith only [inc u v hu hv h,neg_abs_le (F x u-F x v)]
    · simp [h]
    · rw [abs_of_nonneg (sub_nonneg.mpr h.le)]
      linarith only [inc v u hv hu h,le_abs_self (F x u-F x v)]
  have val (x : X) : ∃t∈Ioo S T,F x t=H := by
    exact intermediate_value_Ioo st.le (fun t ht => (df x t ht).1.continuousAt.continuousWithinAt)
      ⟨left x,right x⟩
  choose τ inside eq using val
  have bound (x y : X) : |τ x-τ y|≤8*|F x (τ y)-F y (τ y)| := by
    have m := metric x (τ x) (τ y) (Ioo_subset_Icc_self (inside x)) (Ioo_subset_Icc_self (inside y))
    rwa [eq y,abs_sub_comm (F x (τ y)),←eq x]
  refine ⟨τ,continuous_iff_continuousAt.mpr (fun x => ?_),?_,bound⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    have cont := (hc (τ x) (Ioo_subset_Icc_self (inside x))).continuousAt (x:=x)
    filter_upwards [Metric.tendsto_nhds.mp cont (ε/8) (by positivity)] with y hy
    rw [Real.dist_eq] at hy ⊢
    linarith [bound y x]
  · intro x
    refine ⟨inside x,eq x,?_⟩
    intro t ht h
    have m := metric x t (τ x) ht (Ioo_subset_Icc_self (inside x))
    rw [eq x,h,sub_self,abs_zero,mul_zero] at m
    exact sub_eq_zero.mp (abs_nonpos_iff.mp m)

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.transverse_time
