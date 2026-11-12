import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0500_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0010
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0500_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0500_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0500_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0500_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0500_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨66304059056005778160898227424745040718750886897294969360422734296905315508946337,83208687⟩,⟨219495832606138616518443873992036291985369718827769928735588189299194460090444202,95010155⟩,⟨-23280626183597060898743099858676530007431832429705846573001084806921320916640939,49384951⟩,⟨-9111116534191347249118538153496852283825253561397514025375704205112651173838457,63801967⟩,⟨7903812749146811477189984030292527289372282075899540493463069168249427583412663,21995817⟩,⟨-1884986293949054143909629291069083150429197246153848975858212574695454972346580,13262870⟩,⟨372279741837711207494205276180753045851459734142041881193730875035596080256594956,31944349⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨26736910545751401122118705845493672598553775808701719405011861488583433741608556,268165274⟩,⟨189833421115364391791242094220726755508491811713246435910569385431917538040755299,317144128⟩,⟨-16079676781181817823612627455196826359102233399582983128442912923186054643618868,153404436⟩,⟨-19142726937735969658051479013321029418595843176191736017916866979160013728332425,170122583⟩,⟨4808258784367743584213507138259208162670183306810152338287867343300840755558650,63510176⟩,⟨-1216558598236854029802892754439541947885260012710225649993527222350039965858922,29708966⟩,⟨394914536411609456520584303044952739815596307510370036809915424581797104547570190,111171861⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0500_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0500_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0500_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0010
