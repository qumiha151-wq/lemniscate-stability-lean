import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0005
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨24938191763066988911274359594283807578087849464594208972176106627972514795583370,202088⟩,⟨117631405237039638852881392404799459029554974449586802729517602331001217663929458,202481⟩,⟨23928826971836269647780383176986154822068598131987975041122714500049206042879286,141740⟩,⟨7239560743023091850147925013569851860709807977671141461712096340385371129337279,152753⟩,⟨-7728473027173560121659922762812335831508665305191376969106526535489930662061591,51426⟩,⟨5379623488340696238452470511734045668912393174754714375176305409157379620718139,32458⟩,⟨118760977850279989361174361079172509342956005370607595138605804212581663536802985,61653⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨74410945529556449893728884401847546835342569358422468342638666913550988211036589,579251⟩,⟨123830848533827514136642823601455109050024252891216372291310594341184220695933278,719377⟩,⟨24897828455411095575254604543758980223603665098861332762829239046823772847391843,219753⟩,⟨2257905712141571856790976592963590509974558251953859723475115990739172780625400,379139⟩,⟨2369537029564904046541397985734444439798595280315716802984830445027434082765323,136892⟩,⟨4614159619900903858855781141004871445978319373729402451688994174375383138979958,52845⟩,⟨143518408348922581784737299381163172045064020175448198892050173469281557389753543,250918⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0005
