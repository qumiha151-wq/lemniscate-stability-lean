import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0700_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0014
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0700_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0700_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0700_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0700_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0700_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-20558179781793703033934930146047171975614449632045461965301637347222085725515481,4677855090⟩,⟨49900539377603756958294507095446742709129674065847677691565965972351467835740116,3184444018⟩,⟨-2269715638730426298398467704552215530215254267734951032483623807375699045689481,1818534894⟩,⟨-24896754626242002085746969023539706361776068006152001815648527376049882454078592,860296857⟩,⟨1256363397232375782837149912457175044661236080166478050633465406683763896880153,560720234⟩,⟨-181038345466120966657406956792934303188189703933991666559359401475387746307410,165417359⟩,⟨389377527345019154378528594440910249512509843556007412602012162112535815532420631,2627785259⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-22768860997835500478084554606245865225865264726649950436516214101361802935872330,9766386938⟩,⟨-1821447081328529732368010128625988181457694509215954972,5195505656⟩,⟨-9028421498044529240375083987996038033010232492492509325,3413993283⟩,⟨-24999999999999999999999999999999999999999999999998369752105072947569876279628567,1153707288⟩,⟨1078121152389093060191862144302888631766392922036737523573676907003868356093842,974734987⟩,⟨-16283137061478065077178539541082689023193364687614846,251216856⟩,⟨378365096320749419634974987069029009042150273104750706956482845606048005838324983,6104148048⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0700_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0700_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0700_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0014
