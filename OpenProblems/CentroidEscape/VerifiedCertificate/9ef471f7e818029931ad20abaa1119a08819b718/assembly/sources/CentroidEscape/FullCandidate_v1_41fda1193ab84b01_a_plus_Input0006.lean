import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0006
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨74410945529556449893728908176125922426526762547276059920136787026405882080584752,579251⟩,⟨123830848533827514136642821600269163168547860703221120545927070625443589461140054,719377⟩,⟨24897828455411095575254604350213228830415888115907370630056920201446501191097192,219753⟩,⟨2257905712141571856790978727184205015017607513876318609348232639890195718749552,379139⟩,⟨2369537029564904046541400853019213349984151425226672921729736982310977721273813,136892⟩,⟨4614159619900903858855781565358441143989694203342761580427741814342149297435204,52845⟩,⟨143518408348922581784737342821731583292094945549332272438771645831433477981972380,250918⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨121553810172798882043011240775772509107031213005586329177858095082701509210022150,1341636⟩,⟨138465272571090522270758707164675655150746682326580510581982198523657947476598801,1966264⟩,⟨20342719032513784072609388369419094010514082608711451105632218779685171052577326,718204⟩,⟨14531819650828365992370091323714409142112835172464893469281584850213185880746171,994833⟩,⟨10450852538172521589435333982289357861014692062742674899247416711233158524981922,310477⟩,⟨3268022784248865384219360364756293941596785041955165393237347515210298663628165,156220⟩,⟨192826182191809906348007932833526416680581090672929130799163773441330409660194598,691846⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0006
