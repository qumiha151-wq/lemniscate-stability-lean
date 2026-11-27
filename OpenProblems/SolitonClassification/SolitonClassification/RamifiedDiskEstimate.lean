import SolitonClassification.RamifiedDiskAlgebra
import SolitonClassification.MeromorphicOrdinaryPole
import Mathlib.Analysis.Complex.Liouville

noncomputable section
open Complex Set Metric
open ClosedSimilarity.MeromorphicCurvature
namespace ClosedSimilarity.RamifiedBounded

theorem closed_disk_curvature_bound {a b x:ℂ} {f:ℂ→ℂ} {d:ℝ} (dp:0<d) (d1:d≤1)
    (hf:AnalyticOnNhd ℂ f (closedBall x d))
    (law:∀z∈ball x d,ordinaryResidual a b f z=0) :
    d*‖f x‖≤diskConstant a b := by
  by_cases zero : f x=0
  · simpa [zero] using (zero_le_one.trans (diskConstant_one a b))
  let rem (w:ℂ) := d-dist w x
  have con : Continuous rem := continuous_const.sub (continuous_id.dist continuous_const)
  obtain ⟨z,hz,maxZ⟩ := (isCompact_closedBall x d).exists_isMaxOn
    ⟨x,mem_closedBall_self dp.le⟩ (con.continuousOn.mul hf.continuousOn.norm)
  let D:=rem z
  have control : d*‖f x‖ ≤ D*‖f z‖ := by
    simpa [D,rem] using (maxZ (mem_closedBall_self dp.le))
  have posD : 0<D := pos_of_mul_pos_left ((mul_pos dp (norm_pos_iff.mpr zero)).trans_le control) (norm_nonneg _)
  have D1 : D≤1 := by dsimp [D,rem];linarith only [dist_nonneg (x:=z) (y:=x),d1]
  have zin : z∈ball x d := by change dist z x<d;exact sub_pos.mp posD
  have half : 0<D/2 := half_pos posD
  have subdisk : closedBall z (D/2)⊆closedBall x d := by
    intro w hw
    have tri := dist_triangle w z x
    change dist w z≤D/2 at hw
    change dist w x≤d
    dsimp [D,rem] at hw posD
    linarith
  have bound (w:ℂ) (hw:w∈sphere z (D/2)) : ‖f w‖≤2*‖f z‖ := by
    have dm : dist w z=D/2 := hw
    have tri := dist_triangle w z x
    have hD : D/2≤rem w := by dsimp [D,rem] at dm ⊢;linarith
    have hwc : w∈closedBall z (D/2) := dm.le
    have htop : rem w*‖f w‖≤D*‖f z‖ := maxZ (subdisk hwc)
    apply le_of_mul_le_mul_left (a:=D/2) _ half
    calc D/2*‖f w‖ ≤ rem w*‖f w‖ := mul_le_mul_of_nonneg_right hD (norm_nonneg _)
         _ ≤ D*‖f z‖ := htop
         _ = D/2*(2*‖f z‖) := by ring
  have est (n:ℕ) := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n half
    (hf.differentiableOn.diffContOnCl_ball subdisk) bound
  apply control.trans
  apply scaled_disk_bound posD D1 _ _ _ _ (law z zin)
  · convert est 1 using 1 <;> norm_num [iteratedDeriv_succ,Nat.factorial]
    ring_nf
  · convert est 2 using 1 <;> norm_num [iteratedDeriv_succ,Nat.factorial]
    ring_nf
  · convert est 3 using 1 <;> norm_num [iteratedDeriv_succ,Nat.factorial]
    ring_nf
  · convert est 4 using 1 <;> norm_num [iteratedDeriv_succ,Nat.factorial]
    ring_nf

/-- A pole-free branch obeys the universal inverse-distance bound.
This includes arbitrary complex coefficients and does not assume a
single-valued continuation outside the disk. -/
theorem disk_curvature_bound {a b x:ℂ} {f:ℂ→ℂ} {d:ℝ} (dp:0<d) (d1:d≤1)
    (hf:AnalyticOnNhd ℂ f (ball x d))
    (law:∀z∈ball x d,ordinaryResidual a b f z=0) :
    d*‖f x‖≤diskConstant a b := by
  by_contra! bad
  have cp := (zero_lt_one.trans_le (diskConstant_one a b))
  have fn : 0<‖f x‖ := pos_of_mul_pos_right (cp.trans bad) dp.le
  let r:=(diskConstant a b/‖f x‖+d)/2
  have lt : diskConstant a b/‖f x‖<d := (div_lt_iff₀ fn).mpr bad
  have rp : 0<r := by dsimp [r];positivity
  have rd : r<d := by dsimp [r];linarith
  have rr := closed_disk_curvature_bound rp (rd.le.trans d1)
    (hf.mono (closedBall_subset_ball rd)) (fun z hz=>law z (ball_subset_ball rd.le hz))
  have st : diskConstant a b/‖f x‖<r := by dsimp [r];linarith
  exact (not_le_of_gt ((div_lt_iff₀ fn).mp st)) rr

#print axioms disk_curvature_bound
end ClosedSimilarity.RamifiedBounded
