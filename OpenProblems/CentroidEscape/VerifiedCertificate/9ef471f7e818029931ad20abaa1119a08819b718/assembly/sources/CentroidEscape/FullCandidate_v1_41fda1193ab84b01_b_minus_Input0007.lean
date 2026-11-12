import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0007
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨121553810172798882043011220628398868807580142516000067662679930450727632688479734,1341636⟩,⟨138465272571090522270758699416291622107068572175133402573449445633100300074592357,1966264⟩,⟨20342719032513784072609393362517917872770072215051188958445579770223458733555393,718204⟩,⟨14531819650828365992370084334004316668258937752628094959115232755898559311494986,994833⟩,⟨10450852538172521589435330564228527757383946576951369775308575258329447170615213,310477⟩,⟨3268022784248865384219360461206864435101214647409393812347833047023043960221271,156220⟩,⟨192826182191809906348007878030791156806670860650100948897909859465866237894396731,691846⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨142905810656662369708731376972837381717207464119996805646753191528682846108492308,5109983⟩,⟨181196357021159584207582875564661222516400079419675081523615331478230090395300868,5852881⟩,⟨-1866787428006226598546677220680881166029892508683283254444833515838665534814353,3869329⟩,⟨24930204666200353866364595118166311393985217704375431835803983693676065236284322,3432289⟩,⟨14166913131363564363366547901797848935036098448513047776399055791433349666476597,1142801⟩,⟨234456938532301383366709714703237230027664761635581016219914637640467151422035,880675⟩,⟨260779358711960011046503782828128239476570358326156615255205316049023156968687044,2050448⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0007
