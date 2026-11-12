import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨1356659135563769418858511758068571204484494564831692057434953161430794910497919,793218604⟩,⟨147012205639035313396651715756728719809133004564007184771879898193605335401086181,822725352⟩,⟨-9656546163276567067638617498889813348208753694045589685091703578492121976701111,403649945⟩,⟨-23059729317503026841970166914910650193381062093864740430135444093969229554865408,347234376⟩,⟨2915638552065264640684033687093992366349460847423255244911081156188388896526214,147578542⟩,⟨-714866182853698828935139153594421888134143812554333705739280585891167025866682,56451754⟩,⟨401397796147287482688438018758515585819071739281094871437903598700047180755465437,355652033⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-13229562225337410659321256542266212989857362343226525805156504034349244498342651,2046245006⟩,⟨99296444290087109208235358378561344681422708591554882668167623551320710798266325,1745321124⟩,⟨-5241552209031479160201715290013239087859261679304324035752859498533034574471566,903022527⟩,⟨-24444347617394030607981150966433891008269615906208311490959904816479272643070449,584361672⟩,⟨1825809130932201423522654084378612368631337106745665255502268505995166747005758,299893490⟩,⟨-398981586478450120082365403800727266368343877908258179297486443062535389117350,99503894⟩,⟨398065086162700116103319599853222266220698280048040378662585079068166845039071368,1023709769⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012
