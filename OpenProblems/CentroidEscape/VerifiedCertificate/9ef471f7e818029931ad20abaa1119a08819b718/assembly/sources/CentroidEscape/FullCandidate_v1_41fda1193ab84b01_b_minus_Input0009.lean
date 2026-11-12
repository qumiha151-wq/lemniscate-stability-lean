import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0009
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨114966423123230619283969278464416692915762178047007048494671507615694056381462522,22989576⟩,⟨219692132293261511725492084907827383225306055238726490245784453111617634843535897,22333408⟩,⟨-22820314836351215293365802858936624835721367438598815886148514848991703075190860,16504864⟩,⟨10209467702569444240350706893354939649561984904676868176311759692233291891662731,16614805⟩,⟨11993138805003814495215284755712914622024527027951918702166012438585476003749023,5558955⟩,⟨-1969207534028157925215881580719500047321469269432625754434135328713068339998572,4265637⟩,⟨326980662634848545404170101369678405661862746543059564607001500030054686860909395,8033844⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨66304059056005778160898227424745040718750886897294969360422734296905315508946337,83208687⟩,⟨219495832606138616518443873992036291985369718827769928735588189299194460090444202,95010155⟩,⟨-23280626183597060898743099858676530007431832429705846573001084806921320916640939,49384951⟩,⟨-9111116534191347249118538153496852283825253561397514025375704205112651173838457,63801967⟩,⟨7903812749146811477189984030292527289372282075899540493463069168249427583412663,21995817⟩,⟨-1884986293949054143909629291069083150429197246153848975858212574695454972346580,13262870⟩,⟨372279741837711207494205276180753045851459734142041881193730875035596080256594956,31944349⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0009
