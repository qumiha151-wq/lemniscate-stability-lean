import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0000
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨136288130730646586724540492564119328606333202087402037713638055288801438726445336,1⟩,⟨0,1⟩,⟨0,1⟩,⟨25000000000000000000000000000000000000000000000000000000000000000000000000000000,1⟩,⟨18823334990463805443406067783363950319427188091710822086277581898697941215690329,1⟩,⟨0,1⟩,⟨0,1⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨106470679385259113411467354641769401357127037879527297956572426181567365888827472,390⟩,⟨35694138938034160032058600005965111216346707954121290838920520773165440022915406,389⟩,⟨-23969828322878252131987104175749037182782957188514545085383066229424972407542165,374⟩,⟨7102628398821351730826627353119532832998494520186607885045165005726227562103921,422⟩,⟨11174926312489208776030326596844888713694456342479150534659928140177285949041394,265⟩,⟨-6179879857098116913936353410386335794094921439958420095468433399125710271589439,216⟩,⟨62675262137764506423514948873833096896110384031496257506880773376218668666950862,204⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0000
