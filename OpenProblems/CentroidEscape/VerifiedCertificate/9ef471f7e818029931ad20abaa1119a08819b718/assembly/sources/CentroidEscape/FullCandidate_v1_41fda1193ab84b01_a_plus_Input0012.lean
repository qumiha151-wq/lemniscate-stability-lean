import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0600_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0012
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨1356659135563769418858525277348385806034760629435978040706786052046007654680894,793218604⟩,⟨147012205639035313396651707651733374603206578051260487987747148610411574191759084,822725352⟩,⟨-9656546163276567067638617768923750152754382389049235690021839992730213696517335,403649945⟩,⟨-23059729317503026841970166801830607470366137424907691529519477259217401073419693,347234376⟩,⟨2915638552065264640684032018411975475577720934408780953760123535957965028610167,147578542⟩,⟨-714866182853698828935139645773874566608154996453800366909051754511600607688747,56451754⟩,⟨401397796147287482688438110282408771528098707487737938289971298011577703799199150,355652033⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-13229562225337410659321247433766852168062824242511663682949050282272607334940324,2046245006⟩,⟨99296444290087109208235351483503887783400486158659806103643323165059387944523137,1745321124⟩,⟨-5241552209031479160201719804211485071138204648831548439322769053379216862445482,903022527⟩,⟨-24444347617394030607981149998463456346197598806442007691102847424450373078592534,584361672⟩,⟨1825809130932201423522651434591902934804002218565647385983480291505353986449355,299893490⟩,⟨-398981586478450120082365870063221329956248468460453413212045626669236970446600,99503894⟩,⟨398065086162700116103319697384027072457320810133500923578963250235085744616081329,1023709769⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0600_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0012
