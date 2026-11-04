import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Local linear estimates for parameter derivatives of a smooth branch
which vanishes when the data are zero. No numerical derivative bounds or
analyticity assumption is needed. -/
noncomputable section
namespace Lemniscate
open Filter Set
open scoped Topology ContDiff

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded linear map commutes with every available iterated derivative. -/
theorem continuous_linear_map_iterated_deriv
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) (g : ℝ → X) (n i : ℕ)
    (hg : ContDiffAt ℝ n g 0) (hi : i ≤ n) :
    L (iteratedDeriv i g 0) = iteratedDeriv i (fun a => L (g a)) 0 := by
  unfold iteratedDeriv
  change L ((iteratedFDeriv ℝ i g 0) (fun _ => 1)) =
    (iteratedFDeriv ℝ i (L ∘ g) 0) (fun _ => 1)
  rw [L.iteratedFDeriv_comp_left hg (by exact_mod_cast hi)]
  rfl

private theorem parameter_derivative_eq
    (F : ℝ × P → E) (S : Set (ℝ × P)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F S) (q : P) (hq : ((0:ℝ),q) ∈ S) (n : ℕ) :
    iteratedDeriv n (fun a : ℝ => F (a,q)) 0 =
      (iteratedFDeriv ℝ n F ((0:ℝ),q)) (fun _ => ((1:ℝ),(0:P))) := by
  let H : ℝ × P → E := fun z => F (z+((0:ℝ),q))
  let A : Set (ℝ × P) := (fun z => z+((0:ℝ),q)) ⁻¹' S
  let L : ℝ →L[ℝ] (ℝ × P) := ContinuousLinearMap.inl ℝ ℝ P
  have hA : IsOpen A := hS.preimage (continuous_id.add continuous_const)
  have hH : ContDiffOn ℝ (n:ℕ) H A :=
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp
      (contDiff_id.add contDiff_const).contDiffOn (fun _ hz => hz)
  have hB : IsOpen (L ⁻¹' A) := hA.preimage L.continuous
  have hL0 : L 0 ∈ A := by simpa only [A,Set.mem_preimage,map_zero,zero_add] using hq
  have hcomp := L.iteratedFDerivWithin_comp_right hH hA.uniqueDiffOn
    hB.uniqueDiffOn hL0 (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hB hL0,
    iteratedFDerivWithin_of_isOpen n hA hL0] at hcomp
  have hHder : iteratedFDeriv ℝ n H (L 0) = iteratedFDeriv ℝ n F ((0:ℝ),q) := by
    simpa only [H,map_zero,zero_add] using
      (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F) n ((0:ℝ),q) 0)
  rw [hHder] at hcomp
  have heval := congrArg (fun D => D (fun _ => (1:ℝ))) hcomp
  simpa only [iteratedDeriv,H,L,Function.comp_def,
    ContinuousLinearMap.inl_apply,Prod.mk_add_mk,add_zero,zero_add,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using heval

/-- Every finite parameter derivative is bounded linearly by the data near
zero, for a C-infinity branch that vanishes on the zero-data axis. -/
theorem smooth_parameter_derivative_estimate
    (F : ℝ × P → E) (S : Set (ℝ × P)) (hS : IsOpen S)
    (h0 : ((0:ℝ),(0:P)) ∈ S) (hF : ContDiffOn ℝ ∞ F S)
    (hzero : ∀ a : ℝ, (a,(0:P)) ∈ S → F (a,0) = 0) (n : ℕ) :
    ∃ ε > 0, ∃ C > 0, ∀ q : P, ‖q‖ < ε →
      ‖iteratedDeriv n (fun a : ℝ => F (a,q)) 0‖ ≤ C*‖q‖ := by
  let L : P →L[ℝ] (ℝ × P) := ContinuousLinearMap.inr ℝ ℝ P
  let D := fun q : P => iteratedFDeriv ℝ n F (L q)
  have hF0 : ContDiffAt ℝ ∞ F ((0:ℝ),(0:P)) :=
    hF.contDiffAt (hS.mem_nhds h0)
  have hD0 : DifferentiableAt ℝ D (0:P) := by
    have hd := hF0.differentiableAt_iteratedFDeriv (m := n)
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
    simpa only [D,L,Function.comp_def,map_zero] using!
      hd.comp (0:P) L.differentiableAt
  obtain ⟨C,hC,hbound⟩ := hD0.isBigO_sub.exists_pos
  have haxis : ∀ᶠ a : ℝ in 𝓝 0, F (a,(0:P)) = 0 := by
    have hc : Continuous (fun a : ℝ => (a,(0:P))) := continuous_id.prodMk continuous_const
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hS.mem_nhds h0)] with a ha
    exact hzero a ha
  have hDzero : (D (0:P)) (fun _ => ((1:ℝ),(0:P))) = 0 := by
    have heq := parameter_derivative_eq F S hS hF (0:P) h0 n
    have hvanish := Filter.EventuallyEq.iteratedDeriv_eq n haxis
    simpa only [D,L,map_zero,iteratedDeriv_fun_const_zero] using! heq.symm.trans hvanish
  have hdom : ∀ᶠ q : P in 𝓝 0, L q ∈ S := by
    have hs : S ∈ 𝓝 (L (0:P)) := by
      change S ∈ 𝓝 ((0:ℝ),(0:P))
      exact hS.mem_nhds h0
    exact L.continuous.continuousAt.preimage_mem_nhds hs
  have hevent : ∀ᶠ q : P in 𝓝 0,
      L q ∈ S ∧ ‖D q-D 0‖ ≤ C*‖q‖ := by
    filter_upwards [hdom,hbound.bound] with q hq hb
    exact ⟨hq,by simpa only [sub_zero] using hb⟩
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε,hε,C,hC,?_⟩
  intro q hq
  have hd := hball (show dist q (0:P) < ε by simpa only [dist_zero_right] using hq)
  have hp := parameter_derivative_eq F S hS hF q hd.1 n
  rw [hp]
  change ‖D q (fun _ => ((1:ℝ),(0:P)))‖ ≤ C*‖q‖
  have heval :
      (D q-D 0) (fun _ => ((1:ℝ),(0:P))) = D q (fun _ => ((1:ℝ),(0:P))) := by
    change D q (fun _ => ((1:ℝ),(0:P)))-D 0 (fun _ => ((1:ℝ),(0:P))) = _
    rw [hDzero,sub_zero]
  calc
    ‖D q (fun _ => ((1:ℝ),(0:P)))‖ = ‖(D q-D 0) (fun _ => ((1:ℝ),(0:P)))‖ :=
      congrArg norm heval.symm
    _ ≤ ‖D q-D 0‖ := by
      simpa only [Prod.norm_def,norm_one,norm_zero,max_eq_left zero_le_one,
        Finset.prod_const_one,mul_one] using
        (D q-D 0).le_opNorm (fun _ => ((1:ℝ),(0:P)))
    _ ≤ C*‖q‖ := hd.2

end Lemniscate
