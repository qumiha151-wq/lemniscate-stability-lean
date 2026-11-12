import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0400_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0008
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0400_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0400_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0400_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0400_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0400_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨142905810656662369708731364488147562028807618478603422390756704415312046318686722,5109983⟩,⟨181196357021159584207582886886757396841246973354419131052748956027761582148143628,5852881⟩,⟨-1866787428006226598546689413632936359661602403643199527441517576713893937456136,3869329⟩,⟨24930204666200353866364594205151359784793790633998182826607437466820407609513787,3432289⟩,⟨14166913131363564363366549279808521310086010464132781448398257808742077207264973,1142801⟩,⟨234456938532301383366708128619188308347916836260241932960988506915382091291721,880675⟩,⟨260779358711960011046503772728768707521821458962224554440606594506784566913405975,2050448⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨114966423123230619283969246654120670966716528302128703063578519351386911772113938,22989576⟩,⟨219692132293261511725492082315750595958367543551891284801058273258653245467478779,22333408⟩,⟨-22820314836351215293365807645223591709140983417451548602424636595407229484689158,16504864⟩,⟨10209467702569444240350696194993510513828275448296206706683447360817188105247434,16614805⟩,⟨11993138805003814495215283004094445922609302907720972519096468697239620044951156,5558955⟩,⟨-1969207534028157925215882812849488370512056873019160645834635793139770322351620,4265637⟩,⟨326980662634848545404170079545161275233752339572765226911647348160524670225510413,8033844⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0400_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0400_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0400_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0008
