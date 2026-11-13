module

public import SolitonClassification.Rotating.PointMatrixCertificate
public import SolitonClassification.Rotating.CandidateInitial

@[expose] public section

/-! A finite integer node check with the intended 2000/4000 reference
point budgets. This supplies true inverse bounds for arbitrary checked
points, and says nothing yet about a whole trajectory or matching nodes. -/
namespace SolitonClassification.Rotating
noncomputable section
open Finset Candidate
set_option Elab.async false

def PointNodeValid (B C : PointMatrix) : Prop :=
  (∀i,∑j : Fin 6,|B j i|≤2000*(mesh:ℤ)) ∧
  (∀i,∑j : Fin 6,|C j i|≤3999*(mesh:ℤ)) ∧
  (∀i,∑j : Fin 6,|pointMatrixDefect mesh C B j i|≤10^100) ∧
  (∀i,∑j : Fin 6,|pointMatrixDefect mesh B C j i|≤10^100)

instance (B C : PointMatrix) : Decidable (PointNodeValid B C) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem PointNodeValid.sound {B C : PointMatrix} (h : PointNodeValid B C) :
    ‖pointMatrixOperator mesh B‖≤2000 ∧ IsUnit (pointMatrixOperator mesh B) ∧
      ‖Ring.inverse (pointMatrixOperator mesh B)‖≤4000 := by
  have hn:=pointMatrixOperator_norm mesh_pos B (by norm_num [mesh] : 0≤2000*(mesh:ℤ)) h.1
  have hu:=pointMatrix_inverse_certificate mesh_pos B C
    (by norm_num [mesh] : 0≤3999*(mesh:ℤ)) (by norm_num : (0:ℤ)≤10^100)
    h.2.1 h.2.2.1 h.2.2.2 (by norm_num [mesh])
  refine ⟨?_,hu.1,?_⟩
  · convert! hn using 1
    norm_num [mesh]
  · exact hu.2.trans (by norm_num [mesh])

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.PointNodeValid.sound
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Point-node 2000/4000 exact integer budget soundness audited."

end
