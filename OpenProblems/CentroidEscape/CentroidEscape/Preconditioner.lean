import CentroidEscape.ShootingRootBridge
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace CentroidEscape
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The same finite matrix defect check used for contraction proves the
preconditioner is injective. A separate inverse certificate is unnecessary. -/
theorem preconditioner_injective_of_defect (B J : E →L[ℝ] E)
    (hdef : ‖ContinuousLinearMap.id ℝ E-B.comp J‖<1) : Function.Injective B := by
  have hcomp : Function.Injective (B.comp J) := by
    intro x y hxy
    have hz : (B.comp J) (x-y)=0 := by rw [map_sub,hxy,sub_self]
    have he : (ContinuousLinearMap.id ℝ E-B.comp J) (x-y)=x-y := by
      simp only [sub_apply,ContinuousLinearMap.id_apply,hz,sub_zero]
    have hn := (ContinuousLinearMap.id ℝ E-B.comp J).le_opNorm (x-y)
    rw [he] at hn
    have hnorm : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hsurj : Function.Surjective (B.comp J) :=
    (LinearMap.injective_iff_surjective (f:=(B.comp J).toLinearMap)).mp hcomp
  have hBsurj : Function.Surjective B := by
    intro y
    obtain ⟨x,hx⟩ := hsurj y
    exact ⟨J x,hx⟩
  exact (LinearMap.injective_iff_surjective (f:=B.toLinearMap)).mpr hBsurj

end
end CentroidEscape

#print axioms CentroidEscape.preconditioner_injective_of_defect

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Preconditioner audit passed for {checked} declarations."
