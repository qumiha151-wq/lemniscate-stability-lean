import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set Filter
open scoped Topology

/-- Prescribe the incoming radius for a whole compact strip of seam shots.
    Only continuity in the curvature parameter and a uniform Lipschitz bound
    in the scale variable are needed. The radius is represented by e=d*a(c,d).
    The inverse is unique on the stated interval and continuous jointly. -/
theorem prescribe_radius {C : Type*} [TopologicalSpace C] {D m K : ℝ}
    (hD : 0 < D) (hm : 0 < m) (hK : 0 ≤ K) (small : D*K ≤ m/2)
    (a : C → ℝ → ℝ) (hc : Continuous (fun z : C × Icc (0:ℝ) D => a z.1 z.2))
    (lower : ∀ c, ∀ d ∈ Icc (0:ℝ) D, m ≤ a c d)
    (lip : ∀ c, ∀ x ∈ Icc (0:ℝ) D, ∀ y ∈ Icc (0:ℝ) D, |a c x-a c y| ≤ K*|x-y|) :
    ∃ g : C × Icc (0:ℝ) (D*m) → ℝ, Continuous g ∧ ∀ z,
      g z ∈ Icc (0:ℝ) D ∧ g z * a z.1 (g z) = z.2 ∧
        ∀ d ∈ Icc (0:ℝ) D, d*a z.1 d = z.2 → d = g z := by
  let f := fun (c : C) (d : ℝ) => d*a c d
  have slope (c : C) {x y : ℝ} (hx : x ∈ Icc (0:ℝ) D)
      (hy : y ∈ Icc (0:ℝ) D) (hxy : x ≤ y) : (m/2)*(y-x) ≤ f c y-f c x := by
    have h := (le_abs_self (a c x-a c y)).trans (lip c x hx y hy)
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at h
    have b := mul_le_mul_of_nonneg_left h hx.1
    have k := (mul_le_mul_of_nonneg_right hx.2 hK).trans small
    have l := mul_le_mul_of_nonneg_right (lower c y hy) (sub_nonneg.mpr hxy)
    have e := mul_le_mul_of_nonneg_right k (sub_nonneg.mpr hxy)
    dsimp [f]; nlinarith only [b,l,e]
  have inverse_bound (c : C) {x y : ℝ} (hx : x ∈ Icc (0:ℝ) D)
      (hy : y ∈ Icc (0:ℝ) D) : |x-y| ≤ (2/m)*|f c x-f c y| := by
    suffices H : m*|x-y| ≤ 2*|f c x-f c y| by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hm).mpr (by linarith only [H])
    rcases le_total x y with H | H
    · rw [abs_of_nonpos (sub_nonpos.mpr H)]
      linarith [slope c hx hy H,neg_abs_le (f c x-f c y)]
    · rw [abs_of_nonneg (sub_nonneg.mpr H)]
      linarith [slope c hy hx H,le_abs_self (f c x-f c y)]
  have cf (c : C) : ContinuousOn (f c) (Icc (0:ℝ) D) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact continuous_subtype_val.mul (hc.comp (continuous_const.prodMk continuous_id))
  have pre (z : C × Icc (0:ℝ) (D*m)) : ∃ d ∈ Icc (0:ℝ) D, f z.1 d = z.2 := by
    apply intermediate_value_Icc hD.le (cf z.1)
    refine ⟨by simpa [f] using z.2.property.1,?_⟩
    exact z.2.property.2.trans (mul_le_mul_of_nonneg_left (lower z.1 D ⟨hD.le,le_rfl⟩) hD.le)
  choose g hg eq using pre
  refine ⟨g,?_,?_⟩
  · rw [continuous_iff_continuousAt]
    intro z
    have ca : Continuous (fun u : C × Icc (0:ℝ) (D*m) => a u.1 (g z)) :=
      hc.comp (continuous_fst.prodMk (continuous_const (y := (⟨g z,hg z⟩ : Icc (0:ℝ) D))))
    have err : Continuous (fun u : C × Icc (0:ℝ) (D*m) =>
        (2/m)*|(u.2:ℝ)-f u.1 (g z)|) :=
      continuous_const.mul ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_const.mul ca)).abs
    have lim := err.tendsto z
    simp only [←eq z,sub_self,abs_zero,mul_zero] at lim
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ lim
    intro u
    rw [Real.dist_eq,← eq u]
    exact inverse_bound u.1 (hg u) (hg z)
  · intro z
    refine ⟨hg z,eq z,?_⟩
    intro d hd h
    have b := inverse_bound z.1 hd (hg z)
    rw [show f z.1 d = z.2 from h,eq z,sub_self,abs_zero,mul_zero] at b
    exact sub_eq_zero.mp (abs_nonpos_iff.mp b)

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.prescribe_radius
