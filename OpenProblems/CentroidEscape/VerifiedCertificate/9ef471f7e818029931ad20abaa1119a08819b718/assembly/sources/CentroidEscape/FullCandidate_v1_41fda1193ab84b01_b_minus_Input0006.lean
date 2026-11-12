import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0006
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨74410945529556449893728884401847546835342569358422468342638666913550988211036589,579251⟩,⟨123830848533827514136642823601455109050024252891216372291310594341184220695933278,719377⟩,⟨24897828455411095575254604543758980223603665098861332762829239046823772847391843,219753⟩,⟨2257905712141571856790976592963590509974558251953859723475115990739172780625400,379139⟩,⟨2369537029564904046541397985734444439798595280315716802984830445027434082765323,136892⟩,⟨4614159619900903858855781141004871445978319373729402451688994174375383138979958,52845⟩,⟨143518408348922581784737299381163172045064020175448198892050173469281557389753543,250918⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨121553810172798882043011220628398868807580142516000067662679930450727632688479734,1341636⟩,⟨138465272571090522270758699416291622107068572175133402573449445633100300074592357,1966264⟩,⟨20342719032513784072609393362517917872770072215051188958445579770223458733555393,718204⟩,⟨14531819650828365992370084334004316668258937752628094959115232755898559311494986,994833⟩,⟨10450852538172521589435330564228527757383946576951369775308575258329447170615213,310477⟩,⟨3268022784248865384219360461206864435101214647409393812347833047023043960221271,156220⟩,⟨192826182191809906348007878030791156806670860650100948897909859465866237894396731,691846⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0006
