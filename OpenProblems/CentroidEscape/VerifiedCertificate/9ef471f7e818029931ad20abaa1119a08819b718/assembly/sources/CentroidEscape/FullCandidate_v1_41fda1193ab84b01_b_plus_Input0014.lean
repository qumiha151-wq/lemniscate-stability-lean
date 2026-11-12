import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0014
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-20558179781793703033935002236025925861080571086516061841727305780592554323527493,4677855090⟩,⟨49900539377603756958294492606588704622503387728860156328651034958885973436033793,3184444018⟩,⟨-2269715638730426298398476282585001501162052612904890829699164977217006550274063,1818534894⟩,⟨-24896754626242002085746968241522312683530003706967638924243474115740692763170630,860296857⟩,⟨1256363397232375782837152460996309752584890984848127957747331497943760379994246,560720234⟩,⟨-181038345466120966657404982755231872458664296332149356461854564651116578949254,165417359⟩,⟨389377527345019154378528472126144847224908226860274741564360054220585214338615150,2627785259⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-22768860997835500478084635962111319135579987248973516403063257931790162395753798,9766386938⟩,⟨-15758149598041325442849783915811382541764124255126926329,5195505656⟩,⟨-8179009848030199958052320924627565282504794222847382346,3413993283⟩,⟨-24999999999999999999999999999999999999999999999998662075958116500107747216969649,1153707288⟩,⟨1078121152389093060191869272484693232471741122658403921578898616777552910553190,974734987⟩,⟨2581084152065825872881068979399822026412323153158209881,251216856⟩,⟨378365096320749419634974825637137493304281296781591786719953655220555337605490399,6104148048⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0014
