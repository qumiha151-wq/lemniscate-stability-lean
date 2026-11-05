import Lemniscate.PeriodicSobolevSpace
import Lemniscate.PeriodicIntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Finite classical circle jets give Sobolev families with the same
parameter regularity, including continuity on closed time intervals. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff ENNReal

variable (T : ℝ) [Fact (0 < T)]

/-- A parameter-dependent full classical derivative jet gives a family
in the actual closed Sobolev space with exactly those coordinates and the
same C^m parameter regularity. Orthogonal projection extends the family
off the parameter set without assuming derivative relations there. -/
theorem periodic_classical_sobolev_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (m : ℕ∞ω) (U : Set E)
    (F : Fin (n+1) → E → C(AddCircle T,ℂ))
    (hF : ∀ j, ContDiffOn ℝ m (F j) U)
    (hderiv : ∀ x ∈ U, ∀ j : Fin n,
      HasCircleDeriv T (F j.castSucc x) (F j.succ x)) :
    ∃ u : E → CircleSobolevSpace T n,
      ContDiffOn ℝ m u U ∧
      ∀ x ∈ U, ∀ j : Fin (n+1),
        circleSobolevCoordinate T n j (u x) = circleContinuousL2 T (F j x) := by
  let A := PiLp 2 (fun _ : Fin (n+1) => CircleL2 T)
  let J : E → A := fun x => WithLp.toLp 2
    (fun j : Fin (n+1) => circleContinuousL2 T (F j x))
  have hJ : ContDiffOn ℝ m J U := by
    apply (contDiffOn_piLp (p := (2:ENNReal))).mpr
    intro j
    exact ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn
      (hF j)
  have hmem (x : E) (hx : x ∈ U) : J x ∈ circleSobolevJetSubmodule T n := by
    apply (circle_sobolev_jet_mem_iff T n (J x)).mpr
    intro j
    exact circle_classical_weak_deriv T (F j.castSucc x) (F j.succ x) (hderiv x hx j)
  let P := (circleSobolevJetSubmodule T n).orthogonalProjectionOnto
  let u : E → CircleSobolevSpace T n := fun x => P (J x)
  refine ⟨u,(P.restrictScalars ℝ).contDiff.comp_contDiffOn hJ,?_⟩
  intro x hx j
  have hfix := (circleSobolevJetSubmodule T n).orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨J x,hmem x hx⟩ : CircleSobolevSpace T n)
  change P (J x) = (⟨J x,hmem x hx⟩ : CircleSobolevSpace T n) at hfix
  change circleSobolevCoordinate T n j (P (J x)) = _
  rw [hfix]
  rfl

end Lemniscate
