import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0250_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0005
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0250_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0250_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0250_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0250_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0250_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨24938191763066988911274383100257442925956338981125081678938087478178822995340771,202088⟩,⟨117631405237039638852881391258342721943294144422893005146428404385003633485056044,202481⟩,⟨23928826971836269647780383972700303145562102999887281848700852717566064200019783,141740⟩,⟨7239560743023091850147922383506115932442265418960875863999615081299894533252263,152753⟩,⟨-7728473027173560121659920766329718262967607939587984316885499621034112412523173,51426⟩,⟨5379623488340696238452471058082949579297438334119660189737439303299067899727004,32458⟩,⟨118760977850279989361174392639845693213861786104678138068929529577462002349665959,61653⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨74410945529556449893728908176125922426526762547276059920136787026405882080584752,579251⟩,⟨123830848533827514136642821600269163168547860703221120545927070625443589461140054,719377⟩,⟨24897828455411095575254604350213228830415888115907370630056920201446501191097192,219753⟩,⟨2257905712141571856790978727184205015017607513876318609348232639890195718749552,379139⟩,⟨2369537029564904046541400853019213349984151425226672921729736982310977721273813,136892⟩,⟨4614159619900903858855781565358441143989694203342761580427741814342149297435204,52845⟩,⟨143518408348922581784737342821731583292094945549332272438771645831433477981972380,250918⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0250_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0250_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0250_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0005
