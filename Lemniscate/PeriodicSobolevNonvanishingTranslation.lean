import Lemniscate.PeriodicSobolevTranslationRegularity

/-! Spatial regularity from an actual translation family with a continuous,
nonvanishing multiplier. In particular the multiplier r+1 includes r=0. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

variable (T : ℝ) [Fact (0 < T)]

/-- Smoothness of the actual L2 translation family gives a continuous full
Sobolev jet wherever its translation multiplier is nonzero. No estimate or
smallness of any higher derivative is needed. -/
theorem circle_continuous_sobolev_of_nonvanishing_translation
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (n : ℕ) (c : C(K,ℝ)) (hc : ∀ t : K, c t ≠ 0)
    (f : C(K,CircleL2 T)) (g : ℝ → C(K,CircleL2 T))
    (hg : ContDiffAt ℝ n g 0)
    (htranslate : ∀ᶠ a : ℝ in 𝓝 0, ∀ t : K,
      g a t = circleL2Translation T ((a*c t:ℝ) : AddCircle T) (f t)) :
    ∃ v : C(K,CircleSobolevSpace T n),
      ∀ t : K, circleSobolevCoordinate T n 0 (v t) = f t := by
  let path : K → ℝ → CircleL2 T := fun t a =>
    circleL2Translation T ((a*c t:ℝ) : AddCircle T) (f t)
  have hpoint (t : K) : ContDiffAt ℝ n (path t) 0 := by
    let L : C(K,CircleL2 T) →L[ℝ] CircleL2 T := ContinuousMap.evalCLM ℝ t
    have heq : path t =ᶠ[𝓝 0] (fun a => L (g a)) := by
      filter_upwards [htranslate] with a ha
      exact (ha t).symm
    exact (L.contDiff.contDiffAt.comp 0 hg).congr_of_eventuallyEq heq
  have hderiv (t : K) (j : Fin (n+1)) :
      iteratedDeriv j.val (path t) 0 = (iteratedDeriv j.val g 0) t := by
    let L : C(K,CircleL2 T) →L[ℝ] CircleL2 T := ContinuousMap.evalCLM ℝ t
    have heq : path t =ᶠ[𝓝 0] (fun a => L (g a)) := by
      filter_upwards [htranslate] with a ha
      exact (ha t).symm
    exact (Filter.EventuallyEq.iteratedDeriv_eq j.val heq).trans
      (continuous_linear_map_iterated_deriv L g n j.val hg
        (Nat.le_of_lt_succ j.isLt)).symm
  let J : K → PiLp 2 (fun _ : Fin (n+1) => CircleL2 T) := fun t =>
    WithLp.toLp 2 (fun j => ((((c t)⁻¹)^j.val:ℝ):ℂ) •
      (iteratedDeriv j.val g 0) t)
  have hjet (t : K) : ∃ u : CircleSobolevSpace T n,
      circleSobolevCoordinate T n 0 u = f t ∧
        (u : PiLp 2 (fun _ : Fin (n+1) => CircleL2 T)) = J t := by
    obtain ⟨u,hu,hcoord⟩ := circle_sobolev_of_translation_contDiffAt T n
      (c t) (hc t) (f t) (hpoint t)
    refine ⟨u,hu,?_⟩
    apply PiLp.ext
    intro j
    exact (hcoord j).trans (congrArg
      (fun z : CircleL2 T => ((((c t)⁻¹)^j.val:ℝ):ℂ) • z) (hderiv t j))
  have hmem (t : K) : J t ∈ circleSobolevJetSubmodule T n := by
    obtain ⟨u,_,hu⟩ := hjet t
    exact hu ▸ u.property
  have hJ : Continuous J := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => CircleL2 T)).comp
    apply continuous_pi
    intro j
    exact (Complex.continuous_ofReal.comp ((c.continuous.inv₀ hc).pow j.val)).smul
      (iteratedDeriv j.val g 0).continuous
  let v : C(K,CircleSobolevSpace T n) := ⟨fun t => ⟨J t,hmem t⟩,hJ.subtype_mk _⟩
  refine ⟨v,?_⟩
  intro t
  obtain ⟨u,hu,hJu⟩ := hjet t
  have hv : v t = u := Subtype.ext hJu.symm
  exact (congrArg (circleSobolevCoordinate T n 0) hv).trans hu

end Lemniscate
