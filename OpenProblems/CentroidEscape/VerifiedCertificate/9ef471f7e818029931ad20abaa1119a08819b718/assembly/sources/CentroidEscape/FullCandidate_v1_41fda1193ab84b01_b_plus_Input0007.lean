import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0350_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0007
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0350_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0350_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0350_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0350_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0350_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨121553810172798882043011245754096157456584512267743774270185159758152266512029668,1341636⟩,⟨138465272571090522270758710732322409361440729182158380049868323600318729964223210,1966264⟩,⟨20342719032513784072609384227127031579795575265218388643826339132176928987624148,718204⟩,⟨14531819650828365992370097122402089100810751719417824559400499935325581575767574,994833⟩,⟨10450852538172521589435337215652254221150980917595273972685910682644430879055051,310477⟩,⟨3268022784248865384219360180775170459192142959978242967848150105026639197057111,156220⟩,⟨192826182191809906348007923889018707794528371394668617864897380727422606294252310,691846⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨142905810656662369708731364215193541651479594777612140241610433004081637510963701,5109983⟩,⟨181196357021159584207582903764970755729771380394623884349453078165985727270156779,5852881⟩,⟨-1866787428006226598546703606562562122469610902604302389556912047959107064346836,3869329⟩,⟨24930204666200353866364593142376988426642597955381598593626393606825303767856807,3432289⟩,⟨14166913131363564363366551001420644729931166000225499156367890533698443124593364,1142801⟩,⟨234456938532301383366706586900299944619402260992667399161934034780536287887879,880675⟩,⟨260779358711960011046503833317791430064292229889552650069590841815440066492227531,2050448⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0350_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0350_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0350_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0007
