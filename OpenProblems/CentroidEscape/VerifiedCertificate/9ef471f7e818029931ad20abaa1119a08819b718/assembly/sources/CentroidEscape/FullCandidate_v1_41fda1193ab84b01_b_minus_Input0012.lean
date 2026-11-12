import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0600_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0012
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0600_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0600_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0600_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0600_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0600_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨1356659135563769418858547454417797257072040615923076479746521295205300910170868,793218604⟩,⟨147012205639035313396651738189270244071051582450545534103209386348131001901120645,822725352⟩,⟨-9656546163276567067638611378861710498362746245619792581245120349536447166075352,403649945⟩,⟨-23059729317503026841970169477747927336180756676831855012743075020182545355147397,347234376⟩,⟨2915638552065264640684036332641379938769397945877574673407278189738107650343845,147578542⟩,⟨-714866182853698828935139804764265897993179053947732469339748083550612488222147,56451754⟩,⟨401397796147287482688438088165659525485743279514108997255506539556610418495964340,355652033⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-13229562225337410659321204123341238851513523114859820306362280778343424637445744,2046245006⟩,⟨99296444290087109208235375816402306697062318361076086246195762079936128566650408,1745321124⟩,⟨-5241552209031479160201705303966531652351963849937651201089032101499372803590523,903022527⟩,⟨-24444347617394030607981153107721766558054610709929955800163549521442197929630184,584361672⟩,⟨1825809130932201423522654804867410282562693219820388350960899596672369671007159,299893490⟩,⟨-398981586478450120082366696658800879307019844192480527258712632036732457079075,99503894⟩,⟨398065086162700116103319690948237401283510800425680196836909014192089315124984923,1023709769⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0600_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0600_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0600_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0012
