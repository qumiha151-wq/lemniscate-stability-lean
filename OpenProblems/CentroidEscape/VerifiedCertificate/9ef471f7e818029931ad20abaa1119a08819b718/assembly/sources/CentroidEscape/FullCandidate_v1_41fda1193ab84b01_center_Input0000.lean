import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0000_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0000
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0000_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0000_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0000_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0000_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0000_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨136288130730646586724540492564119328606333202087402037713638055288801438726445336,1⟩,⟨0,1⟩,⟨0,1⟩,⟨25000000000000000000000000000000000000000000000000000000000000000000000000000000,1⟩,⟨18823334990463805443406067158363950319427188091710822086277581898697941215690329,1⟩,⟨0,1⟩,⟨0,1⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨106470679385259113411467355227889786979691457909908979964663467389827667444730562,390⟩,⟨35694138938034160032058600693483106922753715806493912687367562958142533944426333,389⟩,⟨-23969828322878252131987103981405752325563030666905999897009127996046281737385326,374⟩,⟨7102628398821351730826628008985912454494967337703669570824054472705203698937219,422⟩,⟨11174926312489208776030326712576313709877856004711449487781806263010139938076137,265⟩,⟨-6179879857098116913936352885106300545238555125114724266713711348069893336325346,216⟩,⟨62675262137764506423514949006487055755660486246949856969350922044247535298467499,204⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0000_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0000_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0000_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0000
