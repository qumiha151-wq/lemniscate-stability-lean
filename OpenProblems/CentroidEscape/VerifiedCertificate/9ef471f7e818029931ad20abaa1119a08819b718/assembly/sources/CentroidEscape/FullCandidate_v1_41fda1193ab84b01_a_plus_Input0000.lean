import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0000
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨136288130730646586724540502564119328606333202087402037713638055288801438726445336,1⟩,⟨0,1⟩,⟨0,1⟩,⟨25000000000000000000000000000000000000000000000000000000000000000000000000000000,1⟩,⟨18823334990463805443406067158363950319427188091710822086277581898697941215690329,1⟩,⟨0,1⟩,⟨0,1⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨106470679385259113411467365217417365705927173784605690948453536858396131633341843,390⟩,⟨35694138938034160032058600674608327390366758726003119148623773022938873324825055,389⟩,⟨-23969828322878252131987103992990358900197152623394941221351735557660829888660214,374⟩,⟨7102628398821351730826627969890381168056489299653833948391420315548214776459408,422⟩,⟨11174926312489208776030326765251734160322315670504763248685050869888493600326188,265⟩,⟨-6179879857098116913936352849640230423232766056040096901281787386716549250152835,216⟩,⟨62675262137764506423514954001760393027640628465029205082440346416372974887338339,204⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0000
