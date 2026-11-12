import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0600_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0012
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨1356659135563769418858518517708478505259627597134162432953964542094264364202331,793218604⟩,⟨147012205639035313396651711704231047206169791307633845261664318641488385758379605,822725352⟩,⟨-9656546163276567067638617633906781750481568041547242417404292723855058746553068,403649945⟩,⟨-23059729317503026841970166858370628831873599759386287747138461682347212281853173,347234376⟩,⟨2915638552065264640684032852752983920963590890916078929268117090331077884169009,147578542⟩,⟨-714866182853698828935139399684148227371149404504065508370113732217961090467613,56451754⟩,⟨401397796147287482688438064520462178673585223384416776863678595693381262023748269,355652033⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-13229562225337410659321251988016532578960093292868313185286042923553565509384962,2046245006⟩,⟨99296444290087109208235354931032616232411597375107147329495593584493380979626835,1745321124⟩,⟨-5241552209031479160201717547112362079498733164067657241751458042495396395596182,903022527⟩,⟨-24444347617394030607981150482448673677233607356325328412884005633749114157350859,584361672⟩,⟨1825809130932201423522652759485257651717669662655718762176380884207222340815896,299893490⟩,⟨-398981586478450120082365636931974298162296173184354915353517089431850057182764,99503894⟩,⟨398065086162700116103319648618624669339009545090771291147625580531369137942802560,1023709769⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0012
