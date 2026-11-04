import Lemniscate.PeriodicCoverBalanced
import Lemniscate.PeriodicBlochFullEnergy
import Mathlib.Topology.Algebra.Module.Equiv

/-! A genuine L2 isomorphism assembled from the balanced Bloch components.
Its zero block is the neutral transform, its positive blocks use U*T and its
negative blocks use R*(U*T)*R. Only L2 bounded maps and their actual inverses
are involved. No dissipativity or higher Sobolev bound is assumed here.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped BigOperators ComplexConjugate

private theorem circle_cover_balanced_index_emod (M : ℕ) (j : Fin M) :
    circleCoverBalancedIndex M j % (M:ℤ) = (j.val:ℤ) := by
  have hj : (j.val:ℤ) % (M:ℤ) = (j.val:ℤ) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast j.isLt)
  dsimp only [circleCoverBalancedIndex]
  split_ifs with h <;> simp only [Int.sub_emod_right,hj]

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

private theorem circle_cover_balanced_component_embedding_ne (M : ℕ) (hM : 0 < M)
    (i j : Fin M) (hij : i ≠ j) (g : CircleL2 T) :
    circleCoverComponent T S M hM (circleCoverBalancedIndex M i)
      (circleCoverEmbedding T S M hM (circleCoverBalancedIndex M j) g) = 0 := by
  apply circle_fourier_ext T
  intro n
  have hdisjoint : ¬∃ k : ℤ, circleCoverIndex M (circleCoverBalancedIndex M j) k =
      circleCoverIndex M (circleCoverBalancedIndex M i) n := by
    rintro ⟨k,hk⟩
    have hmod := congrArg (fun z : ℤ => z % (M:ℤ)) hk
    simp only [circleCoverIndex,Int.mul_add_emod_self_left,
      circle_cover_balanced_index_emod] at hmod
    have hval : j.val = i.val := by exact_mod_cast hmod
    exact hij (Fin.ext hval).symm
  rw [circle_cover_component_fourier,
    circle_cover_embedding_fourier_zero T S M hM (circleCoverBalancedIndex M j) _ g hdisjoint,
    circle_fourierCoeff_zero]

/-- The finite block map uses the existing lift and component CLMs. -/
def circleCoverBalancedBlockMap (M : ℕ) (hM : 0 < M)
    (B : Fin M → (CircleL2 T →L[ℂ] CircleL2 T)) : CircleL2 S →L[ℂ] CircleL2 S :=
  ∑ j : Fin M, (circleCoverEmbedding T S M hM (circleCoverBalancedIndex M j)).comp
    ((B j).comp (circleCoverComponent T S M hM (circleCoverBalancedIndex M j)))

theorem circle_cover_balanced_block_map_apply (M : ℕ) (hM : 0 < M)
    (B : Fin M → (CircleL2 T →L[ℂ] CircleL2 T)) (f : CircleL2 S) :
    circleCoverBalancedBlockMap T S M hM B f =
      ∑ j : Fin M, circleCoverEmbedding T S M hM (circleCoverBalancedIndex M j)
        (B j (circleCoverComponent T S M hM (circleCoverBalancedIndex M j) f)) := by
  simp only [circleCoverBalancedBlockMap,sum_apply,ContinuousLinearMap.comp_apply]

theorem circle_cover_balanced_block_map_component (M : ℕ) (hM : 0 < M)
    (B : Fin M → (CircleL2 T →L[ℂ] CircleL2 T)) (f : CircleL2 S) (i : Fin M) :
    circleCoverComponent T S M hM (circleCoverBalancedIndex M i)
        (circleCoverBalancedBlockMap T S M hM B f) =
      B i (circleCoverComponent T S M hM (circleCoverBalancedIndex M i) f) := by
  classical
  rw [circle_cover_balanced_block_map_apply,map_sum]
  rw [Finset.sum_eq_single i]
  · exact circle_cover_component_embedding T S M hM _ _
  · intro j _ hji
    exact circle_cover_balanced_component_embedding_ne T S M hM i j (Ne.symm hji) _
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- An arbitrary finite family of genuine block isomorphisms gives a genuine
isomorphism of the full long-circle L2 space. -/
def circleCoverBalancedBlockEquiv (M : ℕ) (hM : 0 < M)
    (B : Fin M → (CircleL2 T ≃L[ℂ] CircleL2 T)) : CircleL2 S ≃L[ℂ] CircleL2 S := by
  let F := circleCoverBalancedBlockMap T S M hM (fun j => (B j).toContinuousLinearMap)
  let G := circleCoverBalancedBlockMap T S M hM (fun j => (B j).symm.toContinuousLinearMap)
  refine ContinuousLinearEquiv.equivOfInverse F G ?_ ?_
  · intro f
    rw [circle_cover_balanced_block_map_apply T S M hM
      (fun j => (B j).symm.toContinuousLinearMap) (F f)]
    simp only [F,circle_cover_balanced_block_map_component]
    change (∑ j : Fin M,
      circleCoverEmbedding T S M hM (circleCoverBalancedIndex M j)
        ((B j).symm (B j (circleCoverComponent T S M hM
          (circleCoverBalancedIndex M j) f)))) = f
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    exact (circle_cover_balanced_reconstruction_parseval T S M hM f).1.symm
  · intro f
    rw [circle_cover_balanced_block_map_apply T S M hM
      (fun j => (B j).toContinuousLinearMap) (G f)]
    simp only [G,circle_cover_balanced_block_map_component]
    change (∑ j : Fin M,
      circleCoverEmbedding T S M hM (circleCoverBalancedIndex M j)
        (B j ((B j).symm (circleCoverComponent T S M hM
          (circleCoverBalancedIndex M j) f)))) = f
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact (circle_cover_balanced_reconstruction_parseval T S M hM f).1.symm

theorem circle_cover_balanced_block_equiv_component (M : ℕ) (hM : 0 < M)
    (B : Fin M → (CircleL2 T ≃L[ℂ] CircleL2 T)) (f : CircleL2 S) (i : Fin M) :
    circleCoverComponent T S M hM (circleCoverBalancedIndex M i)
        (circleCoverBalancedBlockEquiv T S M hM B f) =
      B i (circleCoverComponent T S M hM (circleCoverBalancedIndex M i) f) :=
  circle_cover_balanced_block_map_component T S M hM _ f i

private def circleNeutralL2Equiv (e : circleH4Domain T) (ψ : CircleL2 T)
    (hunit : inner ℂ (e:CircleL2 T) (e:CircleL2 T) = 1)
    (hnorm : inner ℂ ψ (e:CircleL2 T) = 1) : CircleL2 T ≃L[ℂ] CircleL2 T :=
  ContinuousLinearEquiv.equivOfInverse (neutralTransform e ψ) (neutralTransformInv e ψ)
    (neutral_transform_left_inverse e ψ hunit hnorm)
    (neutral_transform_right_inverse e ψ hunit hnorm)

private def circleReflectionL2Equiv : CircleL2 T ≃L[ℂ] CircleL2 T :=
  ContinuousLinearEquiv.equivOfInverse
    (circleReflectIsometry T).toContinuousLinearMap
    (circleReflectIsometry T).toContinuousLinearMap
    (circle_reflect_involutive T) (circle_reflect_involutive T)

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)

/-- The actual positive-parameter centered change U*T, with inverse T^-1*U. -/
def circleCenteredL2Equiv (ψ : CircleL2 T)
    (hnorm : inner ℂ ψ (circleUnitRotation T q p) = 1) :
    CircleL2 T ≃L[ℂ] CircleL2 T := by
  let e := circleUnitRotationH4 T q p hq hp
  let N := paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr
  have hunit : inner ℂ (e:CircleL2 T) (e:CircleL2 T) = 1 := N.inner_neutral_self
  let U := circleRotationHouseholder T q p
  refine ContinuousLinearEquiv.equivOfInverse
    (U.comp (neutralTransform e ψ)) ((neutralTransformInv e ψ).comp U) ?_ ?_
  · intro f
    change neutralTransformInv e ψ (U (U (neutralTransform e ψ f))) = f
    rw [paper_householder_involutive T q p hq hp he hqreal hpreal hs hc ho hr]
    exact neutral_transform_left_inverse e ψ hunit hnorm f
  · intro f
    change U (neutralTransform e ψ (neutralTransformInv e ψ (U f))) = f
    rw [neutral_transform_right_inverse e ψ hunit hnorm]
    exact paper_householder_involutive T q p hq hp he hqreal hpreal hs hc ho hr f

/-- The zero, positive and negative balanced blocks use T, U*T and R*(U*T)*R. -/
def circleCoverStableBlocks (M : ℕ) (ψ : CircleL2 T)
    (hnorm : inner ℂ ψ (circleUnitRotation T q p) = 1) (j : Fin M) :
    CircleL2 T ≃L[ℂ] CircleL2 T :=
  let e := circleUnitRotationH4 T q p hq hp
  let N := paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr
  let Z := circleNeutralL2Equiv T e ψ N.inner_neutral_self hnorm
  let P := circleCenteredL2Equiv T q p hq hp he hqreal hpreal hs hc ho hr ψ hnorm
  if j.val = 0 then Z
  else if circleCoverBalancedIndex M j < 0 then
    (circleReflectionL2Equiv T).trans (P.trans (circleReflectionL2Equiv T))
  else P

/-- The full cover change of variables is a bounded L2 isomorphism with
the explicit finite-block inverse supplied above. -/
def circleCoverStableMetric (M : ℕ) (hM : 0 < M) (ψ : CircleL2 T)
    (hnorm : inner ℂ ψ (circleUnitRotation T q p) = 1) :
    CircleL2 S ≃L[ℂ] CircleL2 S :=
  circleCoverBalancedBlockEquiv T S M hM
    (circleCoverStableBlocks T q p hq hp he hqreal hpreal hs hc ho hr M ψ hnorm)

theorem circle_cover_stable_metric_bounds (M : ℕ) (hM : 0 < M) (ψ : CircleL2 T)
    (hnorm : inner ℂ ψ (circleUnitRotation T q p) = 1) :
    let V := circleCoverStableMetric T S q p hq hp he hqreal hpreal hs hc ho hr M hM ψ hnorm
    ∃ C : ℝ, 0 < C ∧ ∀ f : CircleL2 S,
      ‖f‖ ≤ C*‖V f‖ ∧ ‖V f‖ ≤ C*‖f‖ := by
  let V := circleCoverStableMetric T S q p hq hp he hqreal hpreal hs hc ho hr M hM ψ hnorm
  let C : ℝ := ‖V.toContinuousLinearMap‖+‖V.symm.toContinuousLinearMap‖+1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hforward : ‖V.toContinuousLinearMap‖ ≤ C := by
    dsimp only [C]
    linarith only [norm_nonneg V.symm.toContinuousLinearMap]
  have hbackward : ‖V.symm.toContinuousLinearMap‖ ≤ C := by
    dsimp only [C]
    linarith only [norm_nonneg V.toContinuousLinearMap]
  refine ⟨C,hC,fun f => ⟨?_,?_⟩⟩
  · calc
      ‖f‖ = ‖V.symm (V f)‖ := by rw [V.symm_apply_apply]
      _ ≤ ‖V.symm.toContinuousLinearMap‖*‖V f‖ := V.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ C*‖V f‖ := mul_le_mul_of_nonneg_right hbackward (norm_nonneg _)
  · exact (V.toContinuousLinearMap.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right hforward (norm_nonneg f))

end Profile
end Lemniscate
