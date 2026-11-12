import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0350_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0007
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨121553810172798882043011233191247513132082327391874155235885293413646611091122203,1341636⟩,⟨138465272571090522270758705074307015734254650678644298021551325340563440772086328,1966264⟩,⟨20342719032513784072609388794822474726282823740136282299749369534571889678389007,718204⟩,⟨14531819650828365992370090728203202884534844736022993683974296264463686770291789,994833⟩,⟨10450852538172521589435333889940390989267463747273404419025709619106526600154464,310477⟩,⟨3268022784248865384219360320991017447146678803694089017078799131011750205345939,156220⟩,⟨192826182191809906348007900959904932300599616022385571350461318576461987994133946,691846⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨142905810656662369708731370594015461684343529448809231305910670876662644265178597,5109983⟩,⟨181196357021159584207582889664815989123085729907151583683144837697577805520096392,5852881⟩,⟨-1866787428006226598546690413621721644249751705644123645708751704984080014388247,3869329⟩,⟨24930204666200353866364594130271649910313907829882000835293359474973458963385965,3432289⟩,⟨14166913131363564363366549451609246832483632224370128912919147218077487927315395,1142801⟩,⟨234456938532301383366708150801768587323533511314455348752530778313252623986997,880675⟩,⟨260779358711960011046503808072959834770431294107857313746822165072623381227590696,2050448⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0007
