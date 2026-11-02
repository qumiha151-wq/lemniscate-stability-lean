import Lemniscate.PeriodicEigenvalueDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! A normalized analytic eigenpair, constructed in principal-inverse
coordinates. All derivative invertibility is supplied as an actual bounded
linear equivalence and is instantiated for the profile separately. -/
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped Topology
variable (T : ℝ) [Fact (0 < T)]

theorem circle_normalized_eigenvalue_derivative_equiv (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (ψ x : CircleL2 T)
    (I : (ℂ × CircleL2 T) ≃L[ℂ] (CircleL2 T × ℂ))
    (hI : ∀ a f, I (a,f) =
      (circlePrincipalBlochCoefficient T h h₁ h₂ p hp 0 f-
        a • circlePrincipalResolvent T (p^4) (by positivity) x,
       inner ℂ ψ (circlePrincipalResolvent T (p^4) (by positivity) f))) :
    ∃ J : (ℂ × (ℂ × CircleL2 T)) ≃L[ℂ] (ℂ × (CircleL2 T × ℂ)),
      HasFDerivAt (circleNormalizedEigenvalueMap T h h₁ h₂ p hp ψ)
        J.toContinuousLinearMap (0,(0,x)) := by
  let B : ℂ →L[ℂ] (CircleL2 T × ℂ) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight
      (circlePrincipalBlochCoefficient T h h₁ h₂ p hp 1 x,0)
  let J := (ContinuousLinearEquiv.refl ℂ ℂ).skewProd I B
  refine ⟨J,?_⟩
  apply (circle_normalized_eigenvalue_map_hasFDerivAt T h h₁ h₂ p hp ψ x).congr_fderiv
  apply ContinuousLinearMap.ext
  rintro ⟨z,a,u⟩
  change (z,(circlePrincipalBlochCoefficient T h h₁ h₂ p hp 0 u+
      z • circlePrincipalBlochCoefficient T h h₁ h₂ p hp 1 x-
      a • circlePrincipalResolvent T (p^4) (by positivity) x,
      inner ℂ ψ (circlePrincipalResolvent T (p^4) (by positivity) u))) =
    (z,I (a,u)+z • (circlePrincipalBlochCoefficient T h h₁ h₂ p hp 1 x,0))
  rw [hI]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change _ = (circlePrincipalBlochCoefficient T h h₁ h₂ p hp 0 u-
        a • circlePrincipalResolvent T (p^4) (by positivity) x)+
          z • circlePrincipalBlochCoefficient T h h₁ h₂ p hp 1 x
      module
    · simp

theorem circle_analytic_eigenpair_exists (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (ψ x : CircleL2 T)
    (hx : circlePrincipalBlochCoefficient T h h₁ h₂ p hp 0 x = 0)
    (hn : inner ℂ ψ (circlePrincipalResolvent T (p^4) (by positivity) x) = 1)
    (I : (ℂ × CircleL2 T) ≃L[ℂ] (CircleL2 T × ℂ))
    (hI : ∀ a f, I (a,f) =
      (circlePrincipalBlochCoefficient T h h₁ h₂ p hp 0 f-
        a • circlePrincipalResolvent T (p^4) (by positivity) x,
       inner ℂ ψ (circlePrincipalResolvent T (p^4) (by positivity) f))) :
    ∃ μ : ℂ → ℂ, ∃ f : ℂ → CircleL2 T,
      AnalyticAt ℂ μ 0 ∧ AnalyticAt ℂ f 0 ∧ μ 0 = 0 ∧ f 0 = x ∧
      (∀ᶠ z in 𝓝 (0:ℂ),
        circlePrincipalBlochFamily T h h₁ h₂ p hp z (f z) =
          μ z • circlePrincipalResolvent T (p^4) (by positivity) (f z) ∧
        inner ℂ ψ (circlePrincipalResolvent T (p^4) (by positivity) (f z)) = 1 ∧
        circlePrincipalResolvent T (p^4) (by positivity) (f z) ≠ 0) ∧
      ∃ U : Set (ℂ × (ℂ × CircleL2 T)), IsOpen U ∧ (0,(0,x)) ∈ U ∧
        ∀ z a u, (z,(a,u)) ∈ U →
          circlePrincipalBlochFamily T h h₁ h₂ p hp z u =
            a • circlePrincipalResolvent T (p^4) (by positivity) u →
          inner ℂ ψ (circlePrincipalResolvent T (p^4) (by positivity) u) = 1 →
          a = μ z ∧ u = f z := by
  let G := circleNormalizedEigenvalueMap T h h₁ h₂ p hp ψ
  let v : ℂ × (ℂ × CircleL2 T) := (0,(0,x))
  have hGv : G v = (0,(0,1)) := by
    simp [G,v,circleNormalizedEigenvalueMap,circlePrincipalBlochFamily,hx,hn]
  obtain ⟨J,hd⟩ := circle_normalized_eigenvalue_derivative_equiv T h h₁ h₂ p hp ψ x I hI
  have han := circle_normalized_eigenvalue_map_analytic T h h₁ h₂ p hp ψ v
  have hs : HasStrictFDerivAt G J.toContinuousLinearMap v := by
    simpa only [← hd.fderiv] using han.hasStrictFDerivAt
  let H := hs.toOpenPartialHomeomorph G
  have hv : v ∈ H.source := hs.mem_toOpenPartialHomeomorph_source
  have hi : AnalyticAt ℂ H.symm (0,(0,1)) := by
    rw [← hGv]
    exact H.analyticAt_symm' hv han hd.fderiv
  let g : ℂ → ℂ × (ℂ × CircleL2 T) := fun z => H.symm (z,(0,1))
  have ht : AnalyticAt ℂ (fun z : ℂ => (z,((0:CircleL2 T),(1:ℂ)))) 0 :=
    analyticAt_id.prod analyticAt_const
  have hg : AnalyticAt ℂ g 0 :=
    hi.comp (f := fun z : ℂ => (z,((0:CircleL2 T),(1:ℂ)))) ht
  have hg0 : g 0 = v := by
    change H.symm (0,(0,1)) = v
    rw [← hGv]
    exact H.left_inv hv
  let μ : ℂ → ℂ := fun z => (g z).2.1
  let f : ℂ → CircleL2 T := fun z => (g z).2.2
  have hμ : AnalyticAt ℂ μ 0 := analyticAt_fst.comp (analyticAt_snd.comp hg)
  have hf : AnalyticAt ℂ f 0 := analyticAt_snd.comp (analyticAt_snd.comp hg)
  refine ⟨μ,f,hμ,hf,?_,?_,?_,H.source,H.open_source,hv,?_⟩
  · change (g 0).2.1 = 0
    rw [hg0]
  · change (g 0).2.2 = x
    rw [hg0]
  · have hevent : ∀ᶠ z in 𝓝 (0:ℂ), (z,((0:CircleL2 T),(1:ℂ))) ∈ H.target :=
      ht.continuousAt.preimage_mem_nhds (H.open_target.mem_nhds
        (by rw [← hGv]; exact H.map_source hv))
    filter_upwards [hevent] with z hz
    have heq : G (g z) = (z,(0,1)) := H.right_inv hz
    have hz' : (g z).1 = z := congrArg Prod.fst heq
    have heq' := congrArg (fun w : ℂ × (CircleL2 T × ℂ) => w.2.1) heq
    have hn' := congrArg (fun w : ℂ × (CircleL2 T × ℂ) => w.2.2) heq
    change circlePrincipalBlochFamily T h h₁ h₂ p hp (g z).1 (f z)-
      μ z • circlePrincipalResolvent T (p^4) (by positivity) (f z) = 0 at heq'
    rw [hz'] at heq'
    change inner ℂ ψ (circlePrincipalResolvent T (p^4) (by positivity) (f z)) = 1 at hn'
    refine ⟨sub_eq_zero.mp heq',hn',?_⟩
    intro hzero
    rw [hzero,inner_zero_right] at hn'
    exact zero_ne_one hn'
  · intro z a u hu heq hnorm
    have hGu : G (z,(a,u)) = (z,(0,1)) := by
      simp only [G,circleNormalizedEigenvalueMap,ContinuousLinearMap.comp_apply,
        innerSL_apply_apply,heq,sub_self,hnorm]
    have hu' : g z = (z,(a,u)) := by
      change H.symm (z,(0,1)) = (z,(a,u))
      rw [← hGu]
      exact H.left_inv hu
    exact ⟨(congrArg (fun w : ℂ × (ℂ × CircleL2 T) => w.2.1) hu').symm,
      (congrArg (fun w : ℂ × (ℂ × CircleL2 T) => w.2.2) hu').symm⟩

end Lemniscate
