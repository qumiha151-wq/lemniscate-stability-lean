import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0650_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0013
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-13229562225337410659321251988016532578960093292868313185286042923553565509384962,2046245006⟩,⟨99296444290087109208235354931032616232411597375107147329495593584493380979626835,1745321124⟩,⟨-5241552209031479160201717547112362079498733164067657241751458042495396395596182,903022527⟩,⟨-24444347617394030607981150482448673677233607356325328412884005633749114157350859,584361672⟩,⟨1825809130932201423522652759485257651717669662655718762176380884207222340815896,299893490⟩,⟨-398981586478450120082365636931974298162296173184354915353517089431850057182764,99503894⟩,⟨398065086162700116103319648618624669339009545090771291147625580531369137942802560,1023709769⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-20558179781793703033934927228287121759406470587478326833022663671327776214642926,4677855090⟩,⟨49900539377603756958294509496262441652356318327817714207301616621442198670636569,3184444018⟩,⟨-2269715638730426298398462349041817819048469614642323022929839720783145043532258,1818534894⟩,⟨-24896754626242002085746969511775457790042814342284775433805977965038186089864973,860296857⟩,⟨1256363397232375782837151631070246903329551888378599924681792554410535517809636,560720234⟩,⟨-181038345466120966657406806957580275378565125504971601334157486452684882713767,165417359⟩,⟨389377527345019154378528545008244413310246996940404472340326304240571782484139924,2627785259⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0013
