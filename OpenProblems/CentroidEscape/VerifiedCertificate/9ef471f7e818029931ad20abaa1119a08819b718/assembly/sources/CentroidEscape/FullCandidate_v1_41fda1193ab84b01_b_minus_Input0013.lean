import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0013
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-13229562225337410659321204123341238851513523114859820306362280778343424637445744,2046245006⟩,⟨99296444290087109208235375816402306697062318361076086246195762079936128566650408,1745321124⟩,⟨-5241552209031479160201705303966531652351963849937651201089032101499372803590523,903022527⟩,⟨-24444347617394030607981153107721766558054610709929955800163549521442197929630184,584361672⟩,⟨1825809130932201423522654804867410282562693219820388350960899596672369671007159,299893490⟩,⟨-398981586478450120082366696658800879307019844192480527258712632036732457079075,99503894⟩,⟨398065086162700116103319690948237401283510800425680196836909014192089315124984923,1023709769⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-20558179781793703033934852220548317657732370088476263465153099633635442839162837,4677855090⟩,⟨49900539377603756958294526385936178682209248926823214692992184616906511993580647,3184444018⟩,⟨-2269715638730426298398448415498634136934886616387106299057441070588361433056590,1818534894⟩,⟨-24896754626242002085746970782028602896555624977593379022523729445081418632218728,860296857⟩,⟨1256363397232375782837150801144184054074212791909095886842296517521277239761811,560720234⟩,⟨-181038345466120966657408631159928678298465954677659157527058664823808034306301,165417359⟩,⟨389377527345019154378528617890343979395585767020510453650403710823362423943126924,2627785259⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0013
