import SolitonClassification.Rotating.FlowFoundation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set Metric
open scoped NNReal Topology
open SolitonClassification.Rotating (clipScalar clipScalar_bound clipScalar_eq_self clipScalar_lipschitz)

abbrev Phase := Fin 4 → ℝ

def rhs (d : ℝ) (x : Phase) : Phase :=
  ![x 1, -(x 0)^3/2-x 2, -x 0*x 3, d+x 0*x 2]

theorem rhs_smooth (d : ℝ) : ContDiff ℝ 1 (rhs d) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [rhs] <;> fun_prop

def clipped (R : ℝ) (x : Phase) : Phase := fun i => clipScalar R (x i)

lemma clipped_norm {R : ℝ} (hR : 0 ≤ R) (x : Phase) : ‖clipped R x‖ ≤ R :=
  (pi_norm_le_iff_of_nonneg hR).mpr fun i => clipScalar_bound hR (x i)

lemma clipped_eq {R : ℝ} {x : Phase} (h : ‖x‖ ≤ R) : clipped R x = x := by
  funext i
  exact clipScalar_eq_self ((norm_le_pi_norm x i).trans h)

lemma clipped_lip (R : ℝ) : LipschitzWith 1 (clipped R) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  simp only [NNReal.coe_one,one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  change ‖clipScalar R (x i)-clipScalar R (y i)‖ ≤ _
  have h := lipschitzWith_iff_norm_sub_le.mp (clipScalar_lipschitz R) (x i) (y i)
  simp only [NNReal.coe_one,one_mul] at h
  exact h.trans (norm_le_pi_norm (x-y) i)

def weight (R : ℝ) (x : Phase) : ℝ := min 1 (max 0 (R+1-‖x‖))

lemma weight_mem (R : ℝ) (x : Phase) : weight R x ∈ Icc 0 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

lemma weight_one {R : ℝ} {x : Phase} (h : ‖x‖ ≤ R) : weight R x = 1 := by
  exact min_eq_left (le_max_of_le_right (by linarith))

lemma weight_zero {R : ℝ} {x : Phase} (h : R+1 ≤ ‖x‖) : weight R x = 0 := by
  simp [weight, max_eq_left (show R+1-‖x‖ ≤ 0 by linarith)]

lemma weight_lip (R : ℝ) : LipschitzWith 1 (weight R) := by
  have h : LipschitzWith 1 (fun x : Phase => R+1-‖x‖) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    rw [NNReal.coe_one,one_mul,show R+1-‖x‖-(R+1-‖y‖) = ‖y‖-‖x‖ by ring,Real.norm_eq_abs,abs_sub_comm]
    exact abs_norm_sub_norm_le _ _
  have he : weight R = (fun x : Phase => min (max (R+1-‖x‖) 0) 1) := by
    funext x; unfold weight; rw [min_comm 1,max_comm 0]
  rw [he]
  exact (h.max_const 0).min_const 1

theorem bounded_scaled_extension (d R : ℝ) (hR : 0 ≤ R) :
    ∃ (g : Phase → Phase) (K M : ℝ≥0),
      LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ M) ∧
      ∀ x, g x = weight R x • rhs d x := by
  let S := R+1
  have hS : 0 ≤ S := by dsimp [S]; linarith
  let ball := closedBall (0 : Phase) S
  have hm (x : Phase) : clipped S x ∈ ball := by
    simpa only [ball, mem_closedBall_iff_norm, sub_zero] using clipped_norm hS x
  obtain ⟨K,hK⟩ := (rhs_smooth d).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : Phase) S) (isCompact_closedBall (0 : Phase) S)
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Phase) S).exists_bound_of_continuousOn
    (rhs_smooth d).continuous.continuousOn
  let B : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  let F := fun x => rhs d (clipped S x)
  have hF (x : Phase) : ‖F x‖ ≤ B := (hM _ (hm x)).trans (le_max_left _ _)
  have hL (x y : Phase) : ‖F x-F y‖ ≤ K*‖x-y‖ := by
    have h := lipschitzOnWith_iff_norm_sub_le.mp hK (hm x) (hm y)
    have hc := lipschitzWith_iff_norm_sub_le.mp (clipped_lip S) x y
    simp only [NNReal.coe_one,one_mul] at hc
    exact h.trans (mul_le_mul_of_nonneg_left hc K.coe_nonneg)
  refine ⟨fun x => weight R x • F x,K+B,B,?_,?_,?_⟩
  · rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    have hw := lipschitzWith_iff_norm_sub_le.mp (weight_lip R) x y
    simp only [NNReal.coe_one,one_mul] at hw
    calc
      ‖weight R x • F x - weight R y • F y‖ =
          ‖weight R x • (F x-F y) + (weight R x-weight R y) • F y‖ := by
            rw [smul_sub,sub_smul]; abel_nf
      _ ≤ ‖weight R x • (F x-F y)‖ + ‖(weight R x-weight R y) • F y‖ := norm_add_le _ _
      _ ≤ 1*(K*‖x-y‖) + ‖x-y‖*B := by
          rw [norm_smul,norm_smul]
          exact add_le_add
            (mul_le_mul (by simpa [Real.norm_eq_abs, abs_of_nonneg (weight_mem R x).1] using
              (weight_mem R x).2) (hL x y) (norm_nonneg _) zero_le_one)
            (mul_le_mul hw (hF y) (norm_nonneg _) (norm_nonneg _))
      _ = ↑(K+B)*‖x-y‖ := by push_cast; ring
  · intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_mem R x).1]
    exact (mul_le_mul_of_nonneg_right (weight_mem R x).2 (norm_nonneg _)).trans
      (by simpa using hF x)
  · intro x
    by_cases h : ‖x‖ ≤ S
    · simp only [F,clipped_eq h]
    · have hz : weight R x = 0 := weight_zero (le_of_not_ge h)
      simp [hz]

end ClosedSimilarity.GlobalSupport
