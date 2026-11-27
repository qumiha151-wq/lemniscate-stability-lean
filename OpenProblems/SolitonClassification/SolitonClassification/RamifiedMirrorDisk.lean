import SolitonClassification.RamifiedLiftDisk
import SolitonClassification.RamifiedPuncturedIdentity

noncomputable section
open Complex Set Filter Metric
open scoped Topology
namespace ClosedSimilarity.RamifiedBounded
open RamifiedCurvature

def mirrorLift (q:ℕ) (p s:ℂ) := p*rootSection q (2-s/p^q)

theorem mirrorLift_center (q:ℕ) {p:ℂ} (np:p≠0) : mirrorLift q p (p^q)=p := by
  simp [mirrorLift,rootSection,pow_ne_zero _ np]
  norm_num

theorem mirrorLift_power {q:ℕ} (hq:0<q) {p:ℂ} (np:p≠0) (s:ℂ) :
    (mirrorLift q p s)^q=2*p^q-s := by
  rw [mirrorLift,mul_pow,root_pow hq]
  field_simp

theorem exists_mirror_radius (q:ℕ) : ∃d:ℝ,1<d ∧ d<2 ∧ d^q<2 := by
  have powcont : ContinuousAt (fun t:ℝ=>t^q) 1 := by fun_prop
  have u : ∀ᶠ t in 𝓝 (1:ℝ),t^q<2 :=
    powcont.tendsto.eventually (gt_mem_nhds (by simp))
  have v : ∀ᶠ t in 𝓝 (1:ℝ),t<2 := gt_mem_nhds (by norm_num)
  have right : ∀ᶠ t in 𝓝[>] (1:ℝ),1<t := self_mem_nhdsWithin
  exact (right.and ((v.and u).filter_mono nhdsWithin_le_nhds)).exists

/-- The reflected sheet stays ordinary on a whole disk containing both
the pole lift and the branch value. -/
theorem mirrorLift_geometry {q:ℕ} (hq:0<q) {p w:ℂ} (np:p≠0) {d:ℝ}
    (small:d^q<2) (hw:‖w‖<d*‖p‖) :
    AnalyticAt ℂ (mirrorLift q p) (w^q) ∧
      mirrorLift q p (w^q)≠0 ∧ ‖mirrorLift q p (w^q)‖<4*‖p‖ := by
  have hp := norm_pos_iff.mpr np
  have pr : p^q≠0 := pow_ne_zero _ np
  have rr : ‖w/p‖<d := by rwa [norm_div,div_lt_iff₀ hp]
  have rat : ‖w^q/p^q‖<2 := by
    rw [←div_pow,norm_pow]
    exact (pow_lt_pow_left₀ rr (norm_nonneg _) hq.ne').trans small
  have re := Complex.abs_re_le_norm (w^q/p^q)
  have reLt := (le_abs_self _).trans re
  have positive : 0<(2-w^q/p^q).re := by rw [sub_re];norm_num;linarith only [rat,reLt]
  have no : (2-w^q/p^q:ℂ)≠0 := by intro h;rw [h,zero_re] at positive;exact lt_irrefl _ positive
  have an : AnalyticAt ℂ (fun s:ℂ=>(2:ℂ)-s/p^q) (w^q) :=
    analyticAt_const.sub (analyticAt_id.div analyticAt_const pr)
  refine ⟨analyticAt_const.mul (an.cpow analyticAt_const (Or.inl positive)),?_,?_⟩
  · apply mul_ne_zero np
    intro van
    exact no (by rw [←root_pow hq (2-w^q/p^q),van,zero_pow hq.ne'])
  · have absB : ‖2-w^q/p^q‖<(4:ℝ) := by
      have tri := norm_sub_le (2:ℂ) (w^q/p^q)
      rw [Complex.norm_ofNat] at tri
      linarith only [rat,tri]
    have le4 : (4:ℝ)≤4^q := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4) (show 1≤q from hq)
    have cap : ‖rootSection q (2-w^q/p^q)‖<4 := by
      apply lt_of_pow_lt_pow_left₀ q (by norm_num)
      rw [←norm_pow,root_pow hq]
      exact absB.trans_le le4
    rw [mirrorLift,norm_mul,mul_comm (4:ℝ)]
    exact mul_lt_mul_of_pos_left cap hp

#print axioms mirrorLift_geometry
end ClosedSimilarity.RamifiedBounded
