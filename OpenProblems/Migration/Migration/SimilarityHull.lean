import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Migration.NearRoundConvexDisk
import Migration.FiniteRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
open Set
open scoped BigOperators
namespace MigrationGeometry.SimilarityHull

/-- Similarity of logarithmic dilation u and rotation-to-dilation ratio b. -/
def sim (O : ℂ) (b u : ℝ) (z : ℂ) : ℂ :=
  O + (Real.exp u : ℂ) * ((Real.cos (b*u) : ℂ) + (Real.sin (b*u) : ℂ)*Complex.I) * (z-O)

/-- One fixed oriented line puts all points of the earlier and later images
in opposite strict half-planes. Nonemptiness automatically excludes f=0. -/
def separated (A B : Set ℂ) : Prop :=
  ∃ f : ℂ →L[ℝ] ℝ, ∃ l : ℝ, (∀ z ∈ A, f z < l) ∧ (∀ z ∈ B, l < f z)

/-- The continuous-linear separator is exactly a Euclidean straight line
with a unit normal. Both normal orientations are available. -/
theorem separated_iff_unit_height {A B : Set ℂ} (hA : A.Nonempty) (hB : B.Nonempty) :
    separated A B ↔ ∃ e : ℂ, ‖e‖ = 1 ∧ ∃ l : ℝ,
      (∀ z ∈ A, inner ℝ e z < l) ∧ (∀ z ∈ B, l < inner ℝ e z) := by
  constructor
  · rintro ⟨f,l,ha,hb⟩
    let w := (InnerProductSpace.toDual ℝ ℂ).symm f
    have hw (z : ℂ) : inner ℝ w z = f z := InnerProductSpace.toDual_symm_apply
    have hne : w ≠ 0 := by
      intro heq
      obtain ⟨x,hx⟩ := hA
      obtain ⟨y,hy⟩ := hB
      have bad := (ha x hx).trans (hb y hy)
      rw [← hw x,← hw y,heq] at bad
      simp at bad
    have hp := norm_pos_iff.mpr hne
    refine ⟨‖w‖⁻¹ • w,by simp [hp.ne'],‖w‖⁻¹*l,?_,?_⟩
    · intro z hz
      rw [real_inner_smul_left,hw]
      exact mul_lt_mul_of_pos_left (ha z hz) (inv_pos.mpr hp)
    · intro z hz
      rw [real_inner_smul_left,hw]
      exact mul_lt_mul_of_pos_left (hb z hz) (inv_pos.mpr hp)
  · rintro ⟨e,_,l,ha,hb⟩
    exact ⟨(InnerProductSpace.toDual ℝ ℂ) e,l,ha,hb⟩

@[simp] theorem sim_zero (O : ℂ) (b : ℝ) (z : ℂ) : sim O b 0 z = z := by simp [sim]
@[simp] theorem sim_center (O : ℂ) (b u : ℝ) : sim O b u O = O := by simp [sim]

theorem continuous_sim (O : ℂ) (b u : ℝ) : Continuous (sim O b u) := by
  unfold sim
  fun_prop

theorem sim_add (O : ℂ) (b u v : ℝ) (z : ℂ) :
    sim O b (u+v) z = sim O b u (sim O b v z) := by
  unfold sim
  rw [mul_add b u v, Real.cos_add, Real.sin_add, Real.exp_add]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
  linear_combination (norm := ring)
    -(Real.exp u : ℂ) * Real.exp v * Real.sin (b*u) * Real.sin (b*v) * (z-O) * Complex.I_sq

/-- A compact planar set has compact ordinary convex hull. Carathéodory
reduces the set of all barycentres to a finite union of compact images. -/
theorem compact_convexHull {K : Set ℂ} (hK : IsCompact K) : IsCompact (convexHull ℝ K) := by
  classical
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let B (n : ℕ) (p : (stdSimplex ℝ (Fin n)) × (Fin n → K)) : ℂ :=
    ∑ i, p.1.val i • (p.2 i : ℂ)
  have compact (n : ℕ) : IsCompact (range (B n)) := by
    apply isCompact_range
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
  let D := Module.finrank ℝ ℂ + 1
  have representation : convexHull ℝ K = ⋃ n ∈ Iic D, range (B n) := by
    ext y
    constructor
    · intro hy
      obtain ⟨ι,hι,z,w,hz,hi,hw,h1,h2⟩ := eq_pos_convex_span_of_mem_convexHull hy
      let _ := hι
      let e := Fintype.equivFin ι
      have hc : Fintype.card ι ≤ D := hi.card_le_finrank_succ.trans
        (Nat.add_le_add_right (vectorSpan ℝ (range z)).finrank_le 1)
      have h1' : ∑ i, w (e.symm i) = 1 := (e.symm.sum_comp w).trans h1
      let W : stdSimplex ℝ (Fin (Fintype.card ι)) := ⟨_, fun i => (hw (e.symm i)).le, h1'⟩
      let Z (i : Fin (Fintype.card ι)) : K := ⟨z (e.symm i), hz ⟨_,rfl⟩⟩
      exact mem_iUnion.mpr ⟨_,mem_iUnion.mpr ⟨hc, ⟨(W,Z),
        (e.symm.sum_comp (fun j => w j • z j)).trans h2⟩⟩⟩
    · intro hy
      obtain ⟨n,hn⟩ := mem_iUnion.mp hy
      obtain ⟨_,⟨⟨w,z⟩,rfl⟩⟩ := mem_iUnion.mp hn
      exact (convex_convexHull ℝ K).sum_mem (fun i _ => w.property.1 i) w.property.2
        (fun i _ => subset_convexHull ℝ K (z i).property)
  rw [representation]
  exact (finite_Iic D).isCompact_biUnion (fun n _ => compact n)

private def simAffine (O : ℂ) (b u : ℝ) : ℂ →ᵃ[ℝ] ℂ :=
  let a : ℂ := (Real.exp u : ℂ) * ((Real.cos (b*u) : ℂ)+(Real.sin (b*u) : ℂ)*Complex.I)
  { toFun := sim O b u
    linear := (LinearMap.mul ℂ ℂ a).restrictScalars ℝ
    map_vadd' := by intro z v; simp [sim, a]; ring }

theorem center_mem_sim_hull {K : Set ℂ} {O : ℂ} (h : O ∈ convexHull ℝ K) (b u : ℝ) :
    O ∈ convexHull ℝ (sim O b u '' K) := by
  change O ∈ convexHull ℝ ((simAffine O b u) '' K)
  rw [← (simAffine O b u).image_convexHull K]
  exact ⟨O,h,sim_center O b u⟩

theorem sim_image_add (K : Set ℂ) (O : ℂ) (b u v : ℝ) :
    sim O b u '' (sim O b v '' K) = sim O b (u+v) '' K := by
  rw [Set.image_image]
  congr 1
  funext z
  exact (sim_add O b u v z).symm

theorem center_mem_sim_hull_iff {K : Set ℂ} (O : ℂ) (b u : ℝ) :
    O ∈ convexHull ℝ (sim O b u '' K) ↔ O ∈ convexHull ℝ K := by
  refine ⟨fun h => ?_,fun h => center_mem_sim_hull h b u⟩
  simpa [sim_image_add] using (center_mem_sim_hull h b (-u))

private theorem separated_not_common {A B : Set ℂ} {p : ℂ}
    (h : separated A B) (ha : p ∈ convexHull ℝ A) (hb : p ∈ convexHull ℝ B) : False := by
  obtain ⟨f,l,hA,hB⟩ := h
  have cA : Convex ℝ {z : ℂ | f z < l} := (convex_Iio l).linear_preimage f.toLinearMap
  have cB : Convex ℝ {z : ℂ | l < f z} := (convex_Ioi l).linear_preimage f.toLinearMap
  have lhs : f p < l := convexHull_min hA cA ha
  have rhs : l < f p := convexHull_min hB cB hb
  exact (not_lt_of_ge lhs.le) rhs

private theorem sim_real (O : ℂ) (b u : ℝ) (z : ℂ) (c : ℝ)
    (hc : Real.cos (b*u) = c) (hs : Real.sin (b*u)=0) :
    sim O b u z = O + (Real.exp u*c) • (z-O) := by
  simp [sim, hc, hs, Complex.real_smul]

theorem separated_initial_log_slice_iff {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (O : ℂ) (b : ℝ) :
    (∃ v : ℝ, 0 < v ∧ separated K (sim O b v '' K)) ↔ O ∉ convexHull ℝ K := by
  constructor
  · rintro ⟨v,_,h⟩ hO
    exact separated_not_common h hO (center_mem_sim_hull hO b v)
  · intro hO
    obtain ⟨f,l,hl,hu⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ K)
      (compact_convexHull hK).isClosed hO
    have low (z) (hz : z ∈ K) : l < f z := hu z (subset_convexHull ℝ K hz)
    by_cases hb : b=0
    · subst b
      obtain ⟨m,hm,hmax⟩ := hK.exists_isMaxOn hne f.continuous.continuousOn
      let R := (f m-f O+1)/(l-f O)+1
      have hp : 0 < l-f O := sub_pos.mpr hl
      have hm' := low m hm
      have hr : 1<R := by dsimp [R]; linarith [div_pos (show 0<f m-f O+1 by linarith) hp]
      have hreach : f m+1 < f O+R*(l-f O) := by dsimp [R]; field_simp; nlinarith
      refine ⟨Real.log R,Real.log_pos hr,?_⟩
      refine ⟨f,f m+1,fun z hz => lt_of_le_of_lt (hmax hz) (by linarith),?_⟩
      rintro _ ⟨z,hz,rfl⟩
      rw [sim_real O 0 _ z 1 (by simp) (by simp),Real.exp_log (by linarith : 0<R),mul_one,
        map_add,map_smul,map_sub,smul_eq_mul]
      exact hreach.trans (add_lt_add_right (mul_lt_mul_of_pos_left (sub_lt_sub_right (low z hz) (f O))
        (show 0<R by linarith)) (f O))
    · let v := Real.pi/|b|
      have hv : 0<v := div_pos Real.pi_pos (abs_pos.mpr hb)
      have half : Real.cos (b*v) = -1 ∧ Real.sin (b*v) = 0 := by
        rcases lt_or_gt_of_ne hb with hn|hp
        · have id : b*v = -Real.pi := by dsimp [v]; rw [abs_of_neg hn]; field_simp
          simp [id]
        · have id : b*v = Real.pi := by dsimp [v]; rw [abs_of_pos hp]; field_simp
          simp [id]
      refine ⟨v,hv,?_⟩
      refine ⟨-f,-f O,fun z hz => by simpa using neg_lt_neg (hl.trans (low z hz)),?_⟩
      rintro _ ⟨z,hz,rfl⟩
      rw [sim_real O b v z (-1) half.1 half.2]
      simp only [neg_apply,map_add,map_smul,map_sub,smul_eq_mul]
      nlinarith only [mul_pos (Real.exp_pos v) (sub_pos.mpr (hl.trans (low z hz)))]

theorem separated_log_slices_iff {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (O : ℂ) (b : ℝ) :
    (∃ u v : ℝ, 0 ≤ u ∧ u < v ∧ separated (sim O b u '' K) (sim O b v '' K))
      ↔ O ∉ convexHull ℝ K := by
  constructor
  · rintro ⟨u,v,_,_,h⟩ hO
    exact separated_not_common h (center_mem_sim_hull hO b u) (center_mem_sim_hull hO b v)
  · intro hO
    obtain ⟨v,hv,hsep⟩ := (separated_initial_log_slice_iff hK hne O b).mpr hO
    exact ⟨0,v,le_rfl,hv,by simpa using hsep⟩

/-- The earlier time can be required to lie strictly after any prescribed
logarithmic dilation. -/
theorem separated_log_slices_after_iff {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (O : ℂ) (b start : ℝ) :
    (∃ u v : ℝ, start < u ∧ u < v ∧ separated (sim O b u '' K) (sim O b v '' K))
      ↔ O ∉ convexHull ℝ K := by
  constructor
  · rintro ⟨u,v,_,_,h⟩ hO
    exact separated_not_common h (center_mem_sim_hull hO b u) (center_mem_sim_hull hO b v)
  · intro hO
    let w := start+1
    have hh := (separated_log_slices_iff (hK.image (continuous_sim O b w))
      (hne.image (sim O b w)) O b).mpr (fun h => hO ((center_mem_sim_hull_iff O b w).mp h))
    obtain ⟨u,v,hu,huv,h⟩ := hh
    refine ⟨u+w,v+w,by dsimp [w]; linarith,by linarith,?_⟩
    simpa only [sim_image_add] using h

#print axioms compact_convexHull
#print axioms separated_iff_unit_height
#print axioms sim_add
#print axioms center_mem_sim_hull
#print axioms separated_initial_log_slice_iff
#print axioms separated_log_slices_iff
#print axioms separated_log_slices_after_iff
end MigrationGeometry.SimilarityHull
