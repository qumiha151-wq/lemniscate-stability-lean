import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0008
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨142905810656662369708731376972837381717207464119996805646753191528682846108492308,5109983⟩,⟨181196357021159584207582875564661222516400079419675081523615331478230090395300868,5852881⟩,⟨-1866787428006226598546677220680881166029892508683283254444833515838665534814353,3869329⟩,⟨24930204666200353866364595118166311393985217704375431835803983693676065236284322,3432289⟩,⟨14166913131363564363366547901797848935036098448513047776399055791433349666476597,1142801⟩,⟨234456938532301383366709714703237230027664761635581016219914637640467151422035,880675⟩,⟨260779358711960011046503782828128239476570358326156615255205316049023156968687044,2050448⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨114966423123230619283969278464416692915762178047007048494671507615694056381462522,22989576⟩,⟨219692132293261511725492084907827383225306055238726490245784453111617634843535897,22333408⟩,⟨-22820314836351215293365802858936624835721367438598815886148514848991703075190860,16504864⟩,⟨10209467702569444240350706893354939649561984904676868176311759692233291891662731,16614805⟩,⟨11993138805003814495215284755712914622024527027951918702166012438585476003749023,5558955⟩,⟨-1969207534028157925215881580719500047321469269432625754434135328713068339998572,4265637⟩,⟨326980662634848545404170101369678405661862746543059564607001500030054686860909395,8033844⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0008
