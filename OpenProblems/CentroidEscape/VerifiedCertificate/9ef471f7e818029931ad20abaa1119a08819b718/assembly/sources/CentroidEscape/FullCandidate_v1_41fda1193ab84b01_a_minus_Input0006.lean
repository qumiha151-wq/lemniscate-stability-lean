import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0006
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨74410945529556449893728892209246969019827351026543966489587176354335919352498428,579251⟩,⟨123830848533827514136642819923640197052484299172408687581811050198834550259976832,719377⟩,⟨24897828455411095575254604462619791375473479202558137750803187046153143649556578,219753⟩,⟨2257905712141571856790977487681910273578328981417748793823382352001334406144191,379139⟩,⟨2369537029564904046541400805435047406296368409945497858982669443532336932951850,136892⟩,⟨4614159619900903858855781515214326694106254664876147866526089780131871501153710,52845⟩,⟨143518408348922581784737286914853418804861720716249135744432928580948136660362427,250918⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨121553810172798882043011225606722517157133441778161920206307969540917013060282502,1341636⟩,⟨138465272571090522270758702983938376317762619030708098036204996056446888487629044,1966264⟩,⟨20342719032513784072609389220225855442051564871561055837102932978415652565192278,718204⟩,⟨14531819650828365992370090132691996626956854299581137753719175330076462985536263,994833⟩,⟨10450852538172521589435333797591424117520235431804169401256680752591345404289725,310477⟩,⟨3268022784248865384219360277225740952696572565433018887340934077805573239394579,156220⟩,⟨192826182191809906348007869086283447920618141371842039446547739967377029590331344,691846⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0006
