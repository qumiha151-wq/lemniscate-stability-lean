import Migration.SimilarityHull

noncomputable section
open Set
open scoped Pointwise
namespace MigrationGeometry.SimilarityHull

/-- A complex multiplier encodes an independently chosen angle and dilation. -/
def directSimilarity (O a z : ℂ) : ℂ := O + a*(z-O)

private def directAffine (O a : ℂ) : ℂ →ᵃ[ℝ] ℂ where
  toFun := directSimilarity O a
  linear := (LinearMap.mul ℂ ℂ a).restrictScalars ℝ
  map_vadd' := by intro z v; simp [directSimilarity]; ring

theorem center_mem_direct_hull {K : Set ℂ} {O : ℂ} (h : O ∈ convexHull ℝ K) (a : ℂ) :
    O ∈ convexHull ℝ (directSimilarity O a '' K) := by
  change O ∈ convexHull ℝ ((directAffine O a) '' K)
  rw [← (directAffine O a).image_convexHull]
  exact ⟨O,h,by simp [directAffine,directSimilarity]⟩

theorem not_separated_of_common_hull {A B : Set ℂ} {p : ℂ}
    (ha : p ∈ convexHull ℝ A) (hb : p ∈ convexHull ℝ B) : ¬ separated A B := by
  rintro ⟨f,l,hA,hB⟩
  have lhs : f p < l := convexHull_min hA ((convex_Iio l).linear_preimage f.toLinearMap) ha
  have rhs : l < f p := convexHull_min hB ((convex_Ioi l).linear_preimage f.toLinearMap) hb
  exact (not_lt_of_ge lhs.le) rhs

/-- Allow an error on the later image, with no restriction on its
parametrisation. The reference hull separation margin is its true distance
from O. The earlier image can be any subset of the stated ball. -/
theorem separated_of_similarity_error {A B K : Set ℂ} (hK : IsCompact K)
    (O a : ℂ) {R ε : ℝ} (early : ∀ x ∈ A, dist x O ≤ R)
    (fit : ∀ y ∈ B, ∃ x ∈ K, dist y (directSimilarity O a x) ≤ ε)
    (gap : R+ε < ‖a‖*Metric.infDist O (convexHull ℝ K)) : separated A B := by
  let P := directAffine O a
  let D : Set ℂ := P '' convexHull ℝ K + Metric.closedBall 0 ε
  have hc : Convex ℝ D := ((convex_convexHull ℝ K).affine_image P).add (convex_closedBall _ _)
  have hk : IsCompact D := ((compact_convexHull hK).image
    (show Continuous P from (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))))).add
    (isCompact_closedBall _ _)
  have disj : Disjoint (Metric.closedBall O R) D := by
    rw [Set.disjoint_left]
    rintro _ he ⟨_,⟨x,hx,rfl⟩,q,hq,rfl⟩
    change dist (directSimilarity O a x+q) O ≤ R at he
    have hq' : ‖q‖ ≤ ε := by simpa using hq
    have ht := dist_triangle (directSimilarity O a x) (directSimilarity O a x+q) O
    have hn : dist (directSimilarity O a x) O = ‖a‖ * dist O x := by
      simp [directSimilarity, dist_eq_norm, norm_sub_rev x O]
    have hmove : dist (directSimilarity O a x) (directSimilarity O a x + q) = ‖q‖ := by
      simp [dist_eq_norm]
    rw [hn,hmove] at ht
    linarith only [ht,he,hq',gap,mul_le_mul_of_nonneg_left
      (Metric.infDist_le_dist_of_mem (x := O) hx) (norm_nonneg a)]
  obtain ⟨f,l,r,hl,hgap,hr⟩ := geometric_hahn_banach_compact_closed
    (convex_closedBall O R) (isCompact_closedBall _ _) hc hk.isClosed disj
  refine ⟨f,l,fun x hx => hl x (early x hx),?_⟩
  intro y hy
  obtain ⟨x,hx,hfit⟩ := fit y hy
  apply hgap.trans (hr y ?_)
  refine ⟨P x,⟨x,subset_convexHull ℝ K hx,rfl⟩,y-P x,?_,by abel_nf⟩
  change dist (y - directSimilarity O a x) 0 ≤ ε
  simpa [dist_eq_norm] using hfit

/-- Above an explicit threshold, every complex multiplier moves the
reference hull away from the initial containing disk. -/
theorem separated_of_multiplier {K : Set ℂ} (hK : IsCompact K) (O a : ℂ)
    {R : ℝ} (bound : ∀ x ∈ K, dist x O ≤ R)
    (gap : R < ‖a‖*Metric.infDist O (convexHull ℝ K)) :
    separated K (directSimilarity O a '' K) :=
  separated_of_similarity_error hK O a (ε := 0) bound
    (fun _ ⟨x,hx,e⟩ => ⟨x,hx,e ▸ le_of_eq (dist_self _)⟩) (by simpa using gap)

/-- Dilation alone controls eventual separation, even when there is no
function tying the rotation to the scale. -/
theorem eventually_separated_multipliers {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (O : ℂ) (hout : O ∉ convexHull ℝ K) :
    ∃ Q : ℝ, ∀ a : ℂ, Q < ‖a‖ → separated K (directSimilarity O a '' K) := by
  let d := Metric.infDist O (convexHull ℝ K)
  have hd : 0 < d := ((compact_convexHull hK).isClosed.notMem_iff_infDist_pos
    (hne.mono (subset_convexHull ℝ K))).mp hout
  obtain ⟨m,_,hm⟩ := hK.exists_isMaxOn hne
    (show ContinuousOn (fun x => dist x O) K from (continuous_id.dist continuous_const).continuousOn)
  exact ⟨dist m O/d,fun a h => separated_of_multiplier hK O a (fun x hx => hm hx)
    ((div_lt_iff₀ hd).mp h)⟩

/-- Above the radius-to-distance threshold the angle can be arbitrary,
and can vary independently at every logarithmic dilation. -/
theorem eventually_separated_all_angles {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (O : ℂ) (hout : O ∉ convexHull ℝ K) :
    ∃ U : ℝ, ∀ u : ℝ, U < u → ∀ b : ℝ, separated K (sim O b u '' K) := by
  let d := Metric.infDist O (convexHull ℝ K)
  have hd : 0 < d := ((compact_convexHull hK).isClosed.notMem_iff_infDist_pos
    (hne.mono (subset_convexHull ℝ K))).mp hout
  obtain ⟨m,_,hm⟩ := hK.exists_isMaxOn hne
    (show ContinuousOn (fun x => dist x O) K from (continuous_id.dist continuous_const).continuousOn)
  let R := dist m O
  refine ⟨R/d,fun u hu b => ?_⟩
  let angle : ℂ := (Real.cos (b*u) : ℂ)+(Real.sin (b*u) : ℂ)*Complex.I
  have hangle : ‖angle‖ = 1 := by
    have h := Complex.sq_norm angle
    have hr : angle.re = Real.cos (b*u) := by
      simp only [angle,Complex.add_re,Complex.mul_I_re,Complex.ofReal_re,Complex.ofReal_im,neg_zero,add_zero]
    have hi : angle.im = Real.sin (b*u) := by
      simp only [angle,Complex.add_im,Complex.mul_I_im,Complex.ofReal_re,Complex.ofReal_im,zero_add]
    rw [Complex.normSq_apply,hr,hi] at h
    have ht := Real.sin_sq_add_cos_sq (b*u)
    nlinarith only [h,ht,norm_nonneg angle]
  let a : ℂ := (Real.exp u : ℂ)*angle
  apply separated_of_similarity_error (K := K) hK O a (R := R) (ε := 0) (fun x hx => hm hx)
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,hx,le_of_eq (dist_self _)⟩
  · have hlarge := (div_lt_iff₀ hd).mp hu
    have hexp : u < Real.exp u := by linarith [Real.add_one_le_exp u]
    change R+0 < ‖(Real.exp u : ℂ)*angle‖*d
    rw [norm_mul,hangle,mul_one,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,add_zero]
    exact hlarge.trans (mul_lt_mul_of_pos_right hexp hd)

#print axioms separated_of_similarity_error
#print axioms center_mem_direct_hull
#print axioms not_separated_of_common_hull
#print axioms separated_of_multiplier
#print axioms eventually_separated_multipliers
#print axioms eventually_separated_all_angles
end MigrationGeometry.SimilarityHull
