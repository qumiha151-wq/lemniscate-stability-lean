import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0014
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-20558179781793703033934924310527071543198491542914066112610752764124238857141740,4677855090⟩,⟨49900539377603756958294511897078140595582962589789550272987151873540265834809842,3184444018⟩,⟨-2269715638730426298398456993531420107881684961550460267052475027689313997992457,1818534894⟩,⟨-24896754626242002085746970000011209218309560678416317695729808572812876492786666,860296857⟩,⟨1256363397232375782837153349683318761997867696590585824211635001797655699622730,560720234⟩,⟨-181038345466120966657406657122226247568940547075962883093672588852502226495646,165417359⟩,⟨389377527345019154378528495575578577107984150324799160330937634352569315237509903,2627785259⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-22768860997835500478084520125350281170854105681446767522276231171900465958847403,9766386938⟩,⟨1821447081328529732368016213877526029250096524238057386,5195505656⟩,⟨9028421498044529240375082806693769547781843113937619421,3413993283⟩,⟨-24999999999999999999999999999999999999999999999998369752105072947569876280055176,1153707288⟩,⟨1078121152389093060191865923887014018542754284917709165374078903648786305673943,974734987⟩,⟨16283137061478065077178504649409694913359675074220413,251216856⟩,⟨378365096320749419634974897663069977549506563748848705031124815853924810065235034,6104148048⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0014
