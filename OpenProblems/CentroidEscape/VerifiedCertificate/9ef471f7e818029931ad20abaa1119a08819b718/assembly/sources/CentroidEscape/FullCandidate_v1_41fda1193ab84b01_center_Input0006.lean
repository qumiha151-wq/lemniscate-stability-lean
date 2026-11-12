import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0300_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0006
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0300_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0300_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0300_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0300_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0300_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨74410945529556449893728900192686445723177056786910013336615846892028430466776839,579251⟩,⟨123830848533827514136642820761954680110516079937814928426859007994896136701225270,719377⟩,⟨24897828455411095575254604406416510102944683659232762576149720353250064855566117,219753⟩,⟨2257905712141571856790978107433057644297968247647026986928543771759946026403943,379139⟩,⟨2369537029564904046541400829227130378140259917586076175420335674239625307826285,136892⟩,⟨4614159619900903858855781540286383919047974434109450678843402158540520728036778,52845⟩,⟨143518408348922581784737314868292501048478333132790684297402913855391410540134622,250918⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨121553810172798882043011233191247513132082327391874155235885293413646611091122203,1341636⟩,⟨138465272571090522270758705074307015734254650678644298021551325340563440772086328,1966264⟩,⟨20342719032513784072609388794822474726282823740136282299749369534571889678389007,718204⟩,⟨14531819650828365992370090728203202884534844736022993683974296264463686770291789,994833⟩,⟨10450852538172521589435333889940390989267463747273404419025709619106526600154464,310477⟩,⟨3268022784248865384219360320991017447146678803694089017078799131011750205345939,156220⟩,⟨192826182191809906348007900959904932300599616022385571350461318576461987994133946,691846⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0300_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0300_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0300_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0006
