import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0350_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0007
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0350_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0350_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0350_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0350_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0350_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨121553810172798882043011225606722517157133441778161920206307969540917013060282502,1341636⟩,⟨138465272571090522270758702983938376317762619030708098036204996056446888487629044,1966264⟩,⟨20342719032513784072609389220225855442051564871561055837102932978415652565192278,718204⟩,⟨14531819650828365992370090132691996626956854299581137753719175330076462985536263,994833⟩,⟨10450852538172521589435333797591424117520235431804169401256680752591345404289725,310477⟩,⟨3268022784248865384219360277225740952696572565433018887340934077805573239394579,156220⟩,⟨192826182191809906348007869086283447920618141371842039446547739967377029590331344,691846⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨142905810656662369708731364488147562028807618478603422390756704415312046318686722,5109983⟩,⟨181196357021159584207582886886757396841246973354419131052748956027761582148143628,5852881⟩,⟨-1866787428006226598546689413632936359661602403643199527441517576713893937456136,3869329⟩,⟨24930204666200353866364594205151359784793790633998182826607437466820407609513787,3432289⟩,⟨14166913131363564363366549279808521310086010464132781448398257808742077207264973,1142801⟩,⟨234456938532301383366708128619188308347916836260241932960988506915382091291721,880675⟩,⟨260779358711960011046503772728768707521821458962224554440606594506784566913405975,2050448⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0350_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0350_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0350_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0007
