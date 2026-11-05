import Lemniscate.PeriodicSobolevClassicalJet
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Joint smoothness follows from smooth paths in all spatial Sobolev orders.
The operator-valued evaluation is differentiated using the actual bounded
classical spatial jet, with one spare derivative for norm continuity. -/
noncomputable section
namespace Lemniscate
open Set Filter MeasureTheory
open scoped ContDiff Topology

variable (T : ℝ) [Fact (0 < T)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def spatialJetEval (A : E →L[ℝ] C(AddCircle T,ℂ)) (s : ℝ) : E →L[ℝ] ℂ :=
  (ContinuousMap.evalCLM ℝ (s:AddCircle T)).comp A

private theorem spatial_jet_eval_continuous
    (A B : E →L[ℝ] C(AddCircle T,ℂ))
    (hAB : ∀ f,HasCircleDeriv T (A f) (B f)) :
    Continuous (spatialJetEval T A) := by
  have hbound (s t : ℝ) :
      ‖spatialJetEval T A s-spatialJetEval T A t‖ ≤ ‖B‖*‖s-t‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro f
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun x : ℝ => A f (x:AddCircle T)) (s := (univ:Set ℝ))
      (C := ‖B‖*‖f‖) (fun x _ => (hAB f x).differentiableAt)
      (fun x _ => by
        rw [(hAB f x).deriv]
        exact (B f).norm_coe_le_norm _ |>.trans (B.le_opNorm f))
      (convex_univ : Convex ℝ (univ:Set ℝ)) (mem_univ t) (mem_univ s)
    change ‖A f (s:AddCircle T)-A f (t:AddCircle T)‖ ≤ (‖B‖*‖s-t‖)*‖f‖
    convert h using 1 <;> ring
  exact (lipschitzWith_iff_norm_sub_le.mpr hbound :
    LipschitzWith ‖B‖₊ (spatialJetEval T A)).continuous

private theorem spatial_jet_eval_hasDerivAt
    (A B C : E →L[ℝ] C(AddCircle T,ℂ))
    (hAB : ∀ f,HasCircleDeriv T (A f) (B f))
    (hBC : ∀ f,HasCircleDeriv T (B f) (C f)) (s : ℝ) :
    HasDerivAt (spatialJetEval T A) (spatialJetEval T B s) s := by
  have hB := spatial_jet_eval_continuous T B C hBC
  have hprimitive (b : ℝ) :
      spatialJetEval T A b-spatialJetEval T A 0 =
        ∫ r in (0:ℝ)..b,spatialJetEval T B r := by
    apply ContinuousLinearMap.ext
    intro f
    have heval : (∫ r in (0:ℝ)..b,spatialJetEval T B r) f =
        ∫ r in (0:ℝ)..b,spatialJetEval T B r f :=
      ((ContinuousLinearMap.apply ℝ ℂ f).intervalIntegral_comp_comm
        (hB.intervalIntegrable 0 b)).symm
    change A f (b:AddCircle T)-A f (0:AddCircle T) =
      (∫ r in (0:ℝ)..b,spatialJetEval T B r) f
    rw [heval]
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hAB f r)
      (((B f).continuous.comp (AddCircle.continuous_mk' T)).intervalIntegrable 0 b)).symm
  have heq : spatialJetEval T A = fun b =>
      spatialJetEval T A 0+∫ r in (0:ℝ)..b,spatialJetEval T B r := by
    funext b
    exact eq_add_of_sub_eq' (hprimitive b)
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hB.intervalIntegrable 0 s)
    hB.aestronglyMeasurable.stronglyMeasurableAtFilter hB.continuousAt).const_add _

private theorem spatial_jet_eval_contDiff (m : ℕ)
    (A : Fin (m+2) → E →L[ℝ] C(AddCircle T,ℂ))
    (hA : ∀ j : Fin (m+1),∀ f,HasCircleDeriv T (A j.castSucc f) (A j.succ f)) :
    ContDiff ℝ (m:ℕ∞ω) (spatialJetEval T (A 0)) := by
  induction m with
  | zero =>
      exact contDiff_zero.mpr (spatial_jet_eval_continuous T (A 0) (A 1) (hA 0))
  | succ m ih =>
      let B : Fin (m+2) → E →L[ℝ] C(AddCircle T,ℂ) := fun j => A j.succ
      have hB (j : Fin (m+1)) : ∀ f,
          HasCircleDeriv T (B j.castSucc f) (B j.succ f) := by
        simpa only [B,Fin.castSucc_succ] using hA j.succ
      have hd (s : ℝ) := spatial_jet_eval_hasDerivAt T (A 0) (A 1) (A 2)
        (hA 0) (hA 1) s
      have heq : deriv (spatialJetEval T (A 0))=spatialJetEval T (B 0) :=
        funext fun s => (hd s).deriv
      have h := (contDiff_succ_iff_deriv (n := (m:ℕ∞ω))).mpr
        ⟨fun s => (hd s).differentiableAt,by simp,by rw [heq]; exact ih B hB⟩
      simpa only [Nat.cast_add,Nat.cast_one] using h

theorem circle_sobolev_joint_evaluation_contDiff (m : ℕ) :
    ContDiff ℝ (m:ℕ∞ω)
      (fun z : CircleSobolevSpace T (m+2) × ℝ =>
        circleSobolevClassicalJet T (m+1) z.1 0 (z.2:AddCircle T)) := by
  let A : Fin (m+2) → CircleSobolevSpace T (m+2) →L[ℝ] C(AddCircle T,ℂ) :=
    fun j => ((ContinuousLinearMap.proj j).comp
      (circleSobolevClassicalJet T (m+1))).restrictScalars ℝ
  have hA (j : Fin (m+1)) (f : CircleSobolevSpace T (m+2)) :
      HasCircleDeriv T (A j.castSucc f) (A j.succ f) :=
    circle_sobolev_classical_jet_deriv T (m+1) f j
  exact ((spatial_jet_eval_contDiff T m A hA).comp contDiff_snd).clm_apply contDiff_fst

theorem circle_joint_smooth_of_sobolev_paths
    (a : ℝ) (w : ∀ n : ℕ,ℝ → CircleSobolevSpace T (n+2))
    (hw : ∀ n,ContDiffOn ℝ ∞ (w n) (Ici a))
    (Q : ℝ → C(AddCircle T,ℂ))
    (hQ : ∀ n t,a≤t → circleSobolevCoordinate T (n+2) 0 (w n t)=
      circleContinuousL2 T (Q t)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Q z.1 (z.2:AddCircle T))
      (Ici a ×ˢ (univ:Set ℝ)) := by
  apply contDiffOn_infty.mpr
  intro m
  have hpath : ContDiffOn ℝ (m:ℕ∞ω)
      (fun z : ℝ × ℝ => (w m z.1,z.2)) (Ici a ×ˢ (univ:Set ℝ)) :=
    ((contDiffOn_infty.mp (hw m) m).comp contDiffOn_fst
      (fun z hz => hz.1)).prodMk contDiffOn_snd
  have h := (circle_sobolev_joint_evaluation_contDiff T m).comp_contDiffOn hpath
  apply h.congr
  intro z hz
  have hvalue : circleSobolevClassicalJet T (m+1) (w m z.1) 0=Q z.1 := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    exact (circle_sobolev_classical_jet_l2 T (m+1) (w m z.1) 0).trans (hQ m z.1 hz.1)
  exact congrArg (fun f : C(AddCircle T,ℂ) => f (z.2:AddCircle T)) hvalue.symm

end Lemniscate
