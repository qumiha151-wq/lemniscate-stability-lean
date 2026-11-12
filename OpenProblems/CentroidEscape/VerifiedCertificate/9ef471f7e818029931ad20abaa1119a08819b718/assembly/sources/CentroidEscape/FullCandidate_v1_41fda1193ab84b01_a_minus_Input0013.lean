import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-13229562225337410659321256542266212989857362343226525805156504034349244498342651,2046245006⟩,⟨99296444290087109208235358378561344681422708591554882668167623551320710798266325,1745321124⟩,⟨-5241552209031479160201715290013239087859261679304324035752859498533034574471566,903022527⟩,⟨-24444347617394030607981150966433891008269615906208311490959904816479272643070449,584361672⟩,⟨1825809130932201423522654084378612368631337106745665255502268505995166747005758,299893490⟩,⟨-398981586478450120082365403800727266368343877908258179297486443062535389117350,99503894⟩,⟨398065086162700116103319599853222266220698280048040378662585079068166845039071368,1023709769⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-20558179781793703033934924310527071543198491542914066112610752764124238857141740,4677855090⟩,⟨49900539377603756958294511897078140595582962589789550272987151873540265834809842,3184444018⟩,⟨-2269715638730426298398456993531420107881684961550460267052475027689313997992457,1818534894⟩,⟨-24896754626242002085746970000011209218309560678416317695729808572812876492786666,860296857⟩,⟨1256363397232375782837153349683318761997867696590585824211635001797655699622730,560720234⟩,⟨-181038345466120966657406657122226247568940547075962883093672588852502226495646,165417359⟩,⟨389377527345019154378528495575578577107984150324799160330937634352569315237509903,2627785259⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013
