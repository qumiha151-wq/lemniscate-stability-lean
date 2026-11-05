import Lemniscate.PeriodicContinuousSpatialJetFamily
import Lemniscate.PeriodicCurvatureProfileEntry
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! A smooth real-line periodic family along a C1 parameter path has its
actual derivative in the circle continuous-function norm. The velocity
and its norm continuity are constructed from the true derivative. -/
noncomputable section
namespace Lemniscate
open Set Filter
open scoped ContDiff Topology

/-- The actual parameter derivative of a real periodic family gives a
norm-continuous circle velocity along a C1 path. Pointwise evaluation
identifies the supplied circle family, so no circle norm derivative or
periodicity of the parameter derivative is assumed. -/
theorem periodic_smooth_family_path_derivative
    (L : ℝ) [Fact (0<L)]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (U : Set P) (hU : IsOpen U) (H : P × ℝ → ℝ)
    (hH : ContDiffOn ℝ ∞ H (U ×ˢ (univ : Set ℝ)))
    (hperiodic : ∀ p ∈ U, Function.Periodic (fun s => H (p,s)) L)
    (a b : ℝ) (q : ℝ → P) (hq : ContDiffOn ℝ 1 q (Ioo a b))
    (hqU : MapsTo q (Ioo a b) U)
    (Q : ℝ → C(AddCircle L,ℂ))
    (hQ : ∀ t ∈ Ioo a b, ∀ s : ℝ, Q t (s:AddCircle L) = (H (q t,s):ℂ)) :
    ∃ V : ℝ → C(AddCircle L,ℂ), ContinuousOn V (Ioo a b) ∧
      (∀ t ∈ Ioo a b, HasDerivAt Q (V t) t) ∧
      ∀ t ∈ Ioo a b, ∀ s : ℝ,
        V t (s:AddCircle L) = ((fderiv ℝ H (q t,s)) (deriv q t,0):ℂ) := by
  let I := Ioo a b
  let A := U ×ˢ (univ : Set ℝ)
  have hI : IsOpen I := isOpen_Ioo
  have hA : IsOpen A := hU.prod isOpen_univ
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ H) A :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hA).mp hH).2
  have hqAt (t : ℝ) (ht : t ∈ I) : HasDerivAt q (deriv q t) t :=
    ((hq.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have hdq : ContinuousOn (deriv q) I :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := (0:ℕ∞ω)) hI).mp
      (by simpa only [zero_add] using hq)).2.2.continuousOn
  let v : ℝ × ℝ → ℂ := fun z => ((fderiv ℝ H (q z.1,z.2)) (deriv q z.1,0):ℂ)
  have hpoint (t : ℝ) (ht : t ∈ I) (s : ℝ) :
      HasDerivAt (fun r => (H (q r,s):ℂ)) (v (t,s)) t := by
    have hdomain : A ∈ 𝓝 (q t,s) := hA.mem_nhds ⟨hqU ht,mem_univ s⟩
    have hHt : HasFDerivAt H (fderiv ℝ H (q t,s)) (q t,s) :=
      ((hH.contDiffAt hdomain).differentiableAt (by simp)).hasFDerivAt
    have hm : HasDerivAt (fun r : ℝ => (q r,s)) (deriv q t,(0:ℝ)) t :=
      (hqAt t ht).prodMk (hasDerivAt_const t s)
    exact (hHt.comp_hasDerivAt t hm).ofReal_comp
  have hqfst : ContinuousOn (fun z : ℝ × ℝ => q z.1) (I ×ˢ (univ : Set ℝ)) :=
    hq.continuousOn.comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hdqfst : ContinuousOn (fun z : ℝ × ℝ => deriv q z.1) (I ×ˢ (univ : Set ℝ)) :=
    hdq.comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hm : ContinuousOn (fun z : ℝ × ℝ => (q z.1,z.2)) (I ×ˢ (univ : Set ℝ)) :=
    hqfst.prodMk continuous_snd.continuousOn
  have hmaps : MapsTo (fun z : ℝ × ℝ => (q z.1,z.2))
      (I ×ˢ (univ : Set ℝ)) A := fun z hz => ⟨hqU hz.1,mem_univ _⟩
  have hv : ContinuousOn v (I ×ˢ (univ : Set ℝ)) := by
    have harg : ContinuousOn (fun z : ℝ × ℝ => (deriv q z.1,(0:ℝ)))
        (I ×ˢ (univ : Set ℝ)) := hdqfst.prodMk continuousOn_const
    have hr : ContinuousOn
        (fun z : ℝ × ℝ => (fderiv ℝ H (q z.1,z.2)) (deriv q z.1,(0:ℝ)))
        (I ×ˢ (univ : Set ℝ)) := (hD.continuousOn.comp hm hmaps).clm_apply harg
    exact Complex.ofRealCLM.continuous.comp_continuousOn hr
  have hsmooth (t : ℝ) (ht : t ∈ I) : ContDiff ℝ ∞ (fun s => v (t,s)) := by
    have hs : ContDiff ℝ ∞ (fun s => fderiv ℝ H (q t,s)) := by
      apply contDiff_iff_contDiffAt.mpr
      intro s
      have hdomain : A ∈ 𝓝 (q t,s) := hA.mem_nhds ⟨hqU ht,mem_univ s⟩
      exact (hD.contDiffAt hdomain).comp s (contDiffAt_const.prodMk contDiffAt_id)
    have hcast : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff
    have harg : ContDiff ℝ ∞ (fun _ : ℝ => (deriv q t,(0:ℝ))) := contDiff_const
    have hr : ContDiff ℝ ∞
        (fun s : ℝ => (fderiv ℝ H (q t,s)) (deriv q t,(0:ℝ))) := hs.clm_apply harg
    simpa only [v,Function.comp_def] using! hcast.comp hr
  have hvperiodic (t : ℝ) (ht : t ∈ I) : Function.Periodic (fun s => v (t,s)) L := by
    intro s
    have hevent : (fun r => (H (q r,s+L):ℂ)) =ᶠ[𝓝 t]
        (fun r => (H (q r,s):ℂ)) := by
      filter_upwards [hI.mem_nhds ht] with r hr
      exact congrArg Complex.ofReal (hperiodic (q r) (hqU hr) s)
    exact ((hpoint t ht (s+L)).congr_of_eventuallyEq hevent.symm).unique (hpoint t ht s)
  obtain ⟨F,hFc,hFeval,_⟩ := periodic_continuous_spatial_jet_family L 0 I v
    hsmooth hvperiodic (by
      intro j
      have hj : j.val=0 := Nat.lt_one_iff.mp j.isLt
      simpa only [hj,iteratedDeriv_zero] using hv)
  let V : ℝ → C(AddCircle L,ℂ) := F 0
  have hV : ContinuousOn V I := hFc 0
  have hVeval (t : ℝ) (ht : t ∈ I) (s : ℝ) : V t (s:AddCircle L)=v (t,s) := by
    simpa only [V,Fin.val_zero,iteratedDeriv_zero] using! hFeval t ht 0 s
  have hQpoint (t : ℝ) (ht : t ∈ I) (x : AddCircle L) :
      HasDerivAt (fun r => Q r x) (V t x) t := by
    induction x using QuotientAddGroup.induction_on
    rename_i s
    rw [hVeval t ht s]
    have hevent : (fun r => Q r (s:AddCircle L)) =ᶠ[𝓝 t]
        (fun r => (H (q r,s):ℂ)) := by
      filter_upwards [hI.mem_nhds ht] with r hr
      exact hQ r hr s
    exact (hpoint t ht s).congr_of_eventuallyEq hevent
  exact ⟨V,hV,fun t ht => continuous_map_hasDerivAt_of_pointwise Q V a b hV hQpoint t ht,
    hVeval⟩

end Lemniscate
