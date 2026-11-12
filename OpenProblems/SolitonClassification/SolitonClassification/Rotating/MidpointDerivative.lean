import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

namespace SolitonClassification.Rotating
noncomputable section
open Set Filter
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def dyadicQuotient (f : E → F) (x : E) (n : ℕ) (u : E) : F :=
  (2:ℝ)^n • (f (x+(1/2:ℝ)^n • u)-f x)

lemma dyadic_scale_cancel (n : ℕ) : (2:ℝ)^n*(1/2:ℝ)^n=1 := by
  rw [← mul_pow]
  norm_num

lemma dyadicQuotient_step (f : E → F) (x u : E) (n : ℕ) :
    dyadicQuotient f x (n+1) u-dyadicQuotient f x n u =
      (2:ℝ)^(n+1) • (f (x+(1/2:ℝ) • ((1/2:ℝ)^n • u)) -
        (1/2:ℝ) • (f x+f (x+(1/2:ℝ)^n • u))) := by
  simp only [dyadicQuotient, pow_succ, smul_smul]
  rw [mul_comm ((1/2:ℝ)^n) (1/2:ℝ)]
  module

lemma dyadicQuotient_step_bound {f : E → F} {x u : E} {C : ℝ} (n : ℕ)
    (h : ‖f (x+(1/2:ℝ) • ((1/2:ℝ)^n • u)) -
        (1/2:ℝ) • (f x+f (x+(1/2:ℝ)^n • u))‖ ≤ C*‖(1/2:ℝ)^n • u‖^2) :
    dist (dyadicQuotient f x n u) (dyadicQuotient f x (n+1) u) ≤
      (2*C*‖u‖^2)*(1/2:ℝ)^n := by
  rw [dist_comm, dist_eq_norm, dyadicQuotient_step, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)^(n+1))]
  apply (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)^n)]
  have hc := dyadic_scale_cancel n
  calc
    (2:ℝ)^(n+1)*(C*((1/2:ℝ)^n*‖u‖)^2) =
        ((2:ℝ)^n*(1/2:ℝ)^n)*(2*C*‖u‖^2*(1/2:ℝ)^n) := by rw [pow_succ]; ring
    _ = _ := by rw [hc]; ring

theorem dyadicQuotient_converges [CompleteSpace F] {f : E → F} {x : E} {C : ℝ}
    (h : ∀ u, ‖f (x+(1/2:ℝ) • u)-(1/2:ℝ) • (f x+f (x+u))‖ ≤ C*‖u‖^2)
    (u : E) : ∃ v : F, Tendsto (fun n => dyadicQuotient f x n u) atTop (𝓝 v) := by
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_le_geometric (1/2:ℝ) (2*C*‖u‖^2) (by norm_num)
  intro n
  exact dyadicQuotient_step_bound n (h _)

lemma dyadicQuotient_limit_error {f : E → F} {x u : E} {C : ℝ} {v : F}
    (hv : Tendsto (fun n => dyadicQuotient f x n u) atTop (𝓝 v))
    (h : ∀ n, ‖f (x+(1/2:ℝ) • ((1/2:ℝ)^n • u)) -
        (1/2:ℝ) • (f x+f (x+(1/2:ℝ)^n • u))‖ ≤ C*‖(1/2:ℝ)^n • u‖^2) :
    ‖f (x+u)-f x-v‖ ≤ 4*C*‖u‖^2 := by
  have he := dist_le_of_le_geometric_of_tendsto₀ (1/2:ℝ) (2*C*‖u‖^2)
    (by norm_num) (fun n => dyadicQuotient_step_bound n (h n)) hv
  simp only [dyadicQuotient, pow_zero, one_smul, dist_eq_norm] at he
  norm_num at he
  linarith

lemma radial_midpoint_defect_lipschitz {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x u : E) :
    ‖f (x+(1/2:ℝ) • u)-(1/2:ℝ) • (f x+f (x+u))‖ ≤ (K:ℝ)*‖u‖ := by
  have he : f (x+(1/2:ℝ) • u)-(1/2:ℝ) • (f x+f (x+u)) =
      (f (x+(1/2:ℝ) • u)-f x)-(1/2:ℝ) • (f (x+u)-f x) := by module
  rw [he]
  have h1 := hf.dist_le_mul (x+(1/2:ℝ) • u) x
  have h2 := hf.dist_le_mul (x+u) x
  simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h1 h2
  norm_num at h1
  have hn := norm_sub_le (f (x+(1/2:ℝ) • u)-f x) ((1/2:ℝ) • (f (x+u)-f x))
  norm_num [norm_smul, Real.norm_eq_abs] at hn
  nlinarith

lemma radial_midpoint_quadratic_global {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) {x : E} {R C : ℝ} (hR : 0<R)
    (hmid : ∀ a ∈ Metric.ball x R, ∀ b ∈ Metric.ball x R,
      ‖f ((1/2:ℝ) • (a+b))-(1/2:ℝ) • (f a+f b)‖ ≤ C*‖a-b‖^2) :
    ∀ u, ‖f (x+(1/2:ℝ) • u)-(1/2:ℝ) • (f x+f (x+u))‖ ≤
      max C ((K:ℝ)/R)*‖u‖^2 := by
  intro u
  by_cases hu : ‖u‖<R
  · have hxu : x+u ∈ Metric.ball x R := by simpa [Metric.mem_ball, dist_eq_norm] using hu
    have he := hmid x (Metric.mem_ball_self hR) (x+u) hxu
    have hm : (1/2:ℝ) • (x+(x+u))=x+(1/2:ℝ) • u := by module
    rw [hm] at he
    simp only [sub_add_cancel_left, norm_neg] at he
    exact he.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · have hd : (1:ℝ) ≤ ‖u‖/R := (le_div_iff₀ hR).mpr (by simpa using le_of_not_gt hu)
    calc
      ‖f (x+(1/2:ℝ) • u)-(1/2:ℝ) • (f x+f (x+u))‖ ≤ (K:ℝ)*‖u‖ :=
        radial_midpoint_defect_lipschitz hf x u
      _ ≤ (K:ℝ)*‖u‖*(‖u‖/R) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hd
          (mul_nonneg K.coe_nonneg (norm_nonneg u))
      _ = ((K:ℝ)/R)*‖u‖^2 := by ring
      _ ≤ max C ((K:ℝ)/R)*‖u‖^2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

lemma dyadicQuotient_lipschitz {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : E) (n : ℕ) : LipschitzWith K (dyadicQuotient f x n) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have he : dyadicQuotient f x n u-dyadicQuotient f x n v =
      (2:ℝ)^n • (f (x+(1/2:ℝ)^n • u)-f (x+(1/2:ℝ)^n • v)) := by
    unfold dyadicQuotient
    module
  have hd : (x+(1/2:ℝ)^n • u)-(x+(1/2:ℝ)^n • v) = (1/2:ℝ)^n • (u-v) := by module
  have hl := hf.dist_le_mul (x+(1/2:ℝ)^n • u) (x+(1/2:ℝ)^n • v)
  simp only [dist_eq_norm] at hl ⊢
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)^n)]
  rw [hd,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)^n)] at hl
  apply (mul_le_mul_of_nonneg_left hl (by positivity)).trans_eq
  calc
    (2:ℝ)^n*((K:ℝ)*((1/2:ℝ)^n*‖u-v‖)) =
        ((2:ℝ)^n*(1/2:ℝ)^n)*((K:ℝ)*‖u-v‖) := by ring
    _ = _ := by rw [dyadic_scale_cancel,one_mul]

theorem exists_lipschitz_dyadic_limit [CompleteSpace F] {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) {x : E} {R C : ℝ} (hR : 0<R)
    (hmid : ∀ a ∈ Metric.ball x R, ∀ b ∈ Metric.ball x R,
      ‖f ((1/2:ℝ) • (a+b))-(1/2:ℝ) • (f a+f b)‖ ≤ C*‖a-b‖^2) :
    ∃ L : E → F, LipschitzWith K L ∧ L 0=0 ∧
      (∀ u, Tendsto (fun n => dyadicQuotient f x n u) atTop (𝓝 (L u))) ∧
      (∀ u, ‖u‖<R → ‖f (x+u)-f x-L u‖ ≤ 4*C*‖u‖^2) := by
  have hg := radial_midpoint_quadratic_global hf hR hmid
  choose L hL using (fun u => dyadicQuotient_converges hg u)
  refine ⟨L,?_,?_,hL,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    exact le_of_tendsto ((hL u).dist (hL v))
      (Eventually.of_forall fun n => (dyadicQuotient_lipschitz hf x n).dist_le_mul u v)
  · apply tendsto_nhds_unique (hL 0)
    simp [dyadicQuotient]
  · intro u hu
    apply dyadicQuotient_limit_error (hL u)
    intro n
    have hrn : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hnorm : ‖(1/2:ℝ)^n • u‖ < R := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)^n)]
      exact (mul_le_of_le_one_left (norm_nonneg _) hrn).trans_lt hu
    have hxu : x+(1/2:ℝ)^n • u ∈ Metric.ball x R := by
      simpa [Metric.mem_ball,dist_eq_norm] using hnorm
    have hh := hmid x (Metric.mem_ball_self hR) (x+(1/2:ℝ)^n • u) hxu
    have hm : (1/2:ℝ) • (x+(x+(1/2:ℝ)^n • u))=x+(1/2:ℝ) • ((1/2:ℝ)^n • u) := by module
    rw [hm] at hh
    simpa only [sub_add_cancel_left,norm_neg] using hh

theorem dyadic_limit_preserves_midpoints {f : E → F} {x : E} {R C : ℝ}
    (hR : 0<R)
    (hmid : ∀ a ∈ Metric.ball x R, ∀ b ∈ Metric.ball x R,
      ‖f ((1/2:ℝ) • (a+b))-(1/2:ℝ) • (f a+f b)‖ ≤ C*‖a-b‖^2)
    {L : E → F} (hL : ∀ u, Tendsto (fun n => dyadicQuotient f x n u) atTop (𝓝 (L u))) :
    ∀ u v, L ((1/2:ℝ) • (u+v))=(1/2:ℝ) • (L u+L v) := by
  intro u v
  have hr : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hnear (w : E) : ∀ᶠ n : ℕ in atTop, x+(1/2:ℝ)^n • w ∈ Metric.ball x R := by
    have ht : Tendsto (fun n : ℕ => x+(1/2:ℝ)^n • w) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (hr.smul_const w)
    exact ht.eventually (Metric.ball_mem_nhds x hR)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖dyadicQuotient f x n ((1/2:ℝ) • (u+v))-
        (1/2:ℝ) • (dyadicQuotient f x n u+dyadicQuotient f x n v)‖ ≤
      (C*‖u-v‖^2)*(1/2:ℝ)^n := by
    filter_upwards [hnear u,hnear v] with n hu hv
    have hm := hmid _ hu _ hv
    have hp : (1/2:ℝ) • ((x+(1/2:ℝ)^n • u)+(x+(1/2:ℝ)^n • v)) =
        x+(1/2:ℝ)^n • ((1/2:ℝ) • (u+v)) := by module
    have hd : (x+(1/2:ℝ)^n • u)-(x+(1/2:ℝ)^n • v) =
        (1/2:ℝ)^n • (u-v) := by module
    have he : dyadicQuotient f x n ((1/2:ℝ) • (u+v))-
        (1/2:ℝ) • (dyadicQuotient f x n u+dyadicQuotient f x n v) =
        (2:ℝ)^n • (f ((1/2:ℝ) • ((x+(1/2:ℝ)^n • u)+(x+(1/2:ℝ)^n • v)))-
          (1/2:ℝ) • (f (x+(1/2:ℝ)^n • u)+f (x+(1/2:ℝ)^n • v))) := by
      rw [hp]
      unfold dyadicQuotient
      module
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)^n)]
    apply (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
    rw [hd,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)^n)]
    calc
      (2:ℝ)^n*(C*((1/2:ℝ)^n*‖u-v‖)^2) =
          ((2:ℝ)^n*(1/2:ℝ)^n)*(C*‖u-v‖^2*(1/2:ℝ)^n) := by ring
      _ = _ := by rw [dyadic_scale_cancel,one_mul]
  have hb : Tendsto (fun n : ℕ => (C*‖u-v‖^2)*(1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hr
  have hz := squeeze_zero_norm' hbound hb
  have hl := (hL ((1/2:ℝ) • (u+v))).sub (((hL u).add (hL v)).const_smul (1/2:ℝ))
  exact sub_eq_zero.mp (tendsto_nhds_unique hl hz)

/-- A locally quadratic midpoint defect produces a genuine Frechet
derivative. The continuous linear map is constructed from dyadic quotients,
not supplied as a hypothesis. Its local remainder constant is explicit. -/
theorem exists_hasFDerivAt_of_quadratic_midpoints [CompleteSpace F]
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f) {x : E} {R C : ℝ}
    (hR : 0<R) (hC : 0 ≤ C)
    (hmid : ∀ a ∈ Metric.ball x R, ∀ b ∈ Metric.ball x R,
      ‖f ((1/2:ℝ) • (a+b))-(1/2:ℝ) • (f a+f b)‖ ≤ C*‖a-b‖^2) :
    ∃ A : E →L[ℝ] F, HasFDerivAt f A x ∧ ‖A‖ ≤ (K:ℝ) ∧
      ∀ u, ‖u‖<R → ‖f (x+u)-f x-A u‖ ≤ 4*C*‖u‖^2 := by
  obtain ⟨L,hLip,hzero,hconv,herr⟩ := exists_lipschitz_dyadic_limit hf hR hmid
  have hmidL := dyadic_limit_preserves_midpoints hR hmid hconv
  let : Invertible (2:ℝ) := invertibleOfNonzero (by norm_num)
  let Ladd : E →+ F := AddMonoidHom.ofMapMidpoint ℝ ℝ L hzero (by
    intro u v
    simpa only [midpoint_eq_smul_add,invOf_eq_inv,one_div] using hmidL u v)
  have hLc : Continuous Ladd := by
    change Continuous L
    exact hLip.continuous
  let A : E →L[ℝ] F := Ladd.toRealLinearMap hLc
  have hA : ∀ u, A u=L u := fun _ => rfl
  refine ⟨A,?_,?_,?_⟩
  · rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
    intro ε hε
    have hCp : 0 < 4*C+1 := by linarith
    filter_upwards [Metric.ball_mem_nhds (0:E) (lt_min hR (div_pos hε hCp))] with u hu
    have hu' : ‖u‖<min R (ε/(4*C+1)) := by
      simpa only [Metric.mem_ball,dist_zero_right] using hu
    have hsmall := (lt_div_iff₀ hCp).mp (lt_min_iff.mp hu').2
    have hcoef : 4*C*‖u‖ ≤ ε := by linarith [norm_nonneg u]
    have hm := mul_le_mul_of_nonneg_right hcoef (norm_nonneg u)
    have he := herr u (lt_min_iff.mp hu').1
    rw [hA]
    nlinarith
  · apply A.opNorm_le_bound K.coe_nonneg
    intro u
    rw [hA]
    simpa only [hzero,dist_zero_right] using hLip.dist_le_mul u 0
  · simpa only [hA] using herr

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.exists_hasFDerivAt_of_quadratic_midpoints

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Midpoint-derivative audit passed for {checked} declarations."

