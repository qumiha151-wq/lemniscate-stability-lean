import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_Certificate

#print axioms CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.Certificate.smooth_FEF_centroid_escape
open Lean Elab Command in
run_cmd do
  let target := `CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.Certificate.smooth_FEF_centroid_escape
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in (← collectAxioms target) do
    unless allowed.contains axiomName do
      throwError "Full certificate audit failed: {target} depends on {axiomName}"
  logInfo "Strict full certificate audit passed: unconditional smooth FEF centroid escape."
