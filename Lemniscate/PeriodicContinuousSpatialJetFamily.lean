import Lemniscate.PeriodicClassicalSobolevFamily
import Lemniscate.PeriodicSmoothClassicalJet
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Group.Quotient

/-! Joint continuity of real-line spatial jets gives norm-continuous
circle and Sobolev families, also on closed parameter sets. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff Topology

variable (T : ℝ) [Fact (0 < T)]

/-- The actual spatial jet of a smooth periodic family gives continuous
circle representatives and a continuous family in the actual Sobolev
space, with every derivative coordinate identified. Joint continuity on
the real line is sufficient; continuity in the circle supremum norm is
proved by quotient descent and compact-domain currying. -/
theorem periodic_continuous_spatial_jet_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (n : ℕ) (U : Set P) (f : P × ℝ → ℂ)
    (hsmooth : ∀ p ∈ U, ContDiff ℝ ∞ (fun x => f (p,x)))
    (hperiodic : ∀ p ∈ U, Function.Periodic (fun x => f (p,x)) T)
    (hjoint : ∀ j : Fin (n+1),
      ContinuousOn (fun z : P × ℝ => iteratedDeriv j.val (fun x => f (z.1,x)) z.2)
        (U ×ˢ (univ : Set ℝ))) :
    ∃ F : Fin (n+1) → P → C(AddCircle T,ℂ),
      (∀ j, ContinuousOn (F j) U) ∧
      (∀ p ∈ U, ∀ (j : Fin (n+1)) (x : ℝ),
        F j p (x:AddCircle T) = iteratedDeriv j.val (fun s => f (p,s)) x) ∧
      ∃ u : P → CircleSobolevSpace T n, ContinuousOn u U ∧
        ∀ p ∈ U, ∀ j : Fin (n+1),
          circleSobolevCoordinate T n j (u p) = circleContinuousL2 T (F j p) := by
  classical
  let Φ (p : P) (hp : p ∈ U) : ℕ → C(AddCircle T,ℂ) :=
    Classical.choose (periodic_smooth_classical_jet T (fun x => f (p,x))
      (hsmooth p hp) (hperiodic p hp))
  have hΦ (p : P) (hp : p ∈ U) :
      (∀ i : ℕ, ∀ x : ℝ, Φ p hp i (x:AddCircle T) =
        iteratedDeriv i (fun s => f (p,s)) x) ∧
      ∀ i : ℕ, HasCircleDeriv T (Φ p hp i) (Φ p hp (i+1)) :=
    Classical.choose_spec (periodic_smooth_classical_jet T (fun x => f (p,x))
      (hsmooth p hp) (hperiodic p hp))
  let F : Fin (n+1) → P → C(AddCircle T,ℂ) :=
    fun j p => if hp : p ∈ U then Φ p hp j.val else 0
  have hF (p : P) (hp : p ∈ U) (j : Fin (n+1)) : F j p = Φ p hp j.val := by
    dsimp only [F]
    exact dif_pos hp
  have hreal (p : P) (hp : p ∈ U) (j : Fin (n+1)) (x : ℝ) :
      F j p (x:AddCircle T) = iteratedDeriv j.val (fun s => f (p,s)) x :=
    (congrArg (fun g : C(AddCircle T,ℂ) => g (x:AddCircle T)) (hF p hp j)).trans
      ((hΦ p hp).1 j.val x)
  have hqcircle : IsOpenQuotientMap (fun x : ℝ => (x:AddCircle T)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have hq : IsOpenQuotientMap
      (Prod.map (id : U → U) (fun x : ℝ => (x:AddCircle T))) :=
    IsOpenQuotientMap.id.prodMap hqcircle
  have hFc (j : Fin (n+1)) : ContinuousOn (F j) U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hc : Continuous (fun z : U × ℝ =>
        iteratedDeriv j.val (fun s => f ((z.1:P),s)) z.2) := by
      have hi : Continuous (fun z : U × ℝ => ((z.1:P),z.2)) :=
        (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
      simpa only [Function.comp_def] using!
        (hjoint j).comp_continuous hi
          (fun z : U × ℝ => ⟨z.1.property,mem_univ _⟩)
    apply hq.continuous_comp_iff.mp
    change Continuous (fun z : U × ℝ => F j (z.1:P) (z.2:AddCircle T))
    have heq : (fun z : U × ℝ => F j (z.1:P) (z.2:AddCircle T)) =
        fun z : U × ℝ => iteratedDeriv j.val (fun s => f ((z.1:P),s)) z.2 :=
      funext fun z => hreal z.1 z.1.property j z.2
    rw [heq]
    exact hc
  have hderiv (p : P) (hp : p ∈ U) (j : Fin n) :
      HasCircleDeriv T (F j.castSucc p) (F j.succ p) := by
    rw [hF p hp j.castSucc,hF p hp j.succ]
    exact (hΦ p hp).2 j.val
  obtain ⟨u,hu,hcoord⟩ := periodic_classical_sobolev_family T n 0 U F
    (fun j => contDiffOn_zero.mpr (hFc j)) hderiv
  exact ⟨F,hFc,hreal,u,hu.continuousOn,hcoord⟩

end Lemniscate
