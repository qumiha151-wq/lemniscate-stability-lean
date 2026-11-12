import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0006
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨74410945529556449893728915983525344611011544215395841426675091328696482805785677,579251⟩,⟨123830848533827514136642817922454251171007906984414403646351808943317603282352189,719377⟩,⟨24897828455411095575254604269074039982285702219603970259499100259684369247519564,219753⟩,⟨2257905712141571856790979621902524778621378243341619497316333061940062168973840,379139⟩,⟨2369537029564904046541403672719816316481924554856649613938239561956907144334077,136892⟩,⟨4614159619900903858855781939567896392117629494489525212114336529019277682615673,52845⟩,⟨143518408348922581784737330355421830051892646090132898122701910405779833938092210,250918⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨121553810172798882043011245754096157456584512267743774270185159758152266512029668,1341636⟩,⟨138465272571090522270758710732322409361440729182158380049868323600318729964223210,1966264⟩,⟨20342719032513784072609384227127031579795575265218388643826339132176928987624148,718204⟩,⟨14531819650828365992370097122402089100810751719417824559400499935325581575767574,994833⟩,⟨10450852538172521589435337215652254221150980917595273972685910682644430879055051,310477⟩,⟨3268022784248865384219360180775170459192142959978242967848150105026639197057111,156220⟩,⟨192826182191809906348007923889018707794528371394668617864897380727422606294252310,691846⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0006
