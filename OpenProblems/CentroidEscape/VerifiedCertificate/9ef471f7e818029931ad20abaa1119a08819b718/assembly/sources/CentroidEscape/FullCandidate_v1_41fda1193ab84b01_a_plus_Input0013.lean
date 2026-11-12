import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0013
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-13229562225337410659321247433766852168062824242511663682949050282272607334940324,2046245006⟩,⟨99296444290087109208235351483503887783400486158659806103643323165059387944523137,1745321124⟩,⟨-5241552209031479160201719804211485071138204648831548439322769053379216862445482,903022527⟩,⟨-24444347617394030607981149998463456346197598806442007691102847424450373078592534,584361672⟩,⟨1825809130932201423522651434591902934804002218565647385983480291505353986449355,299893490⟩,⟨-398981586478450120082365870063221329956248468460453413212045626669236970446600,99503894⟩,⟨398065086162700116103319697384027072457320810133500923578963250235085744616081329,1023709769⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-20558179781793703033934930146047171975614449632045461965301637347222085725515481,4677855090⟩,⟨49900539377603756958294507095446742709129674065847677691565965972351467835740116,3184444018⟩,⟨-2269715638730426298398467704552215530215254267734951032483623807375699045689481,1818534894⟩,⟨-24896754626242002085746969023539706361776068006152001815648527376049882454078592,860296857⟩,⟨1256363397232375782837149912457175044661236080166478050633465406683763896880153,560720234⟩,⟨-181038345466120966657406956792934303188189703933991666559359401475387746307410,165417359⟩,⟨389377527345019154378528594440910249512509843556007412602012162112535815532420631,2627785259⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0013
