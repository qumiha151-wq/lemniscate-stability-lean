import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-20558179781793703033934852220548317657732370088476263465153099633635442839162837,4677855090⟩,⟨49900539377603756958294526385936178682209248926823214692992184616906511993580647,3184444018⟩,⟨-2269715638730426298398448415498634136934886616387106299057441070588361433056590,1818534894⟩,⟨-24896754626242002085746970782028602896555624977593379022523729445081418632218728,860296857⟩,⟨1256363397232375782837150801144184054074212791909095886842296517521277239761811,560720234⟩,⟨-181038345466120966657408631159928678298465954677659157527058664823808034306301,165417359⟩,⟨389377527345019154378528617890343979395585767020510453650403710823362423943126924,2627785259⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-22768860997835500478084438769484827261139383159169413451956485072218680894299148,9766386938⟩,⟨15758149598041325442849843948225291214531109087649798748,5195505656⟩,⟨8179009848030199958052313244444932481276741306781422038,3413993283⟩,⟨-24999999999999999999999999999999999999999999999998662075958116500107747219482301,1153707288⟩,⟨1078121152389093060191858795705209417837406084296654998334847892341276728686065,974734987⟩,⟨-2581084152065825872881068727371130901687819625868000252,251216856⟩,⟨378365096320749419634975059094961493287375540071966504531232185134490270832115601,6104148048⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014
