import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0450_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0009
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0450_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0450_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0450_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0450_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0450_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨114966423123230619283969246654120670966716528302128703063578519351386911772113938,22989576⟩,⟨219692132293261511725492082315750595958367543551891284801058273258653245467478779,22333408⟩,⟨-22820314836351215293365807645223591709140983417451548602424636595407229484689158,16504864⟩,⟨10209467702569444240350696194993510513828275448296206706683447360817188105247434,16614805⟩,⟨11993138805003814495215283004094445922609302907720972519096468697239620044951156,5558955⟩,⟨-1969207534028157925215882812849488370512056873019160645834635793139770322351620,4265637⟩,⟨326980662634848545404170079545161275233752339572765226911647348160524670225510413,8033844⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨66304059056005778160898194993329196191582252569023696152505817039482180927615184,83208687⟩,⟨219495832606138616518443853262095474669389525823684117635559428345140226439761225,95010155⟩,⟨-23280626183597060898743097518266444336154117465511191378265327981626606599725064,49384951⟩,⟨-9111116534191347249118544133687327991453323123150755274410291386655747321966801,63801967⟩,⟨7903812749146811477189980778642015845320299455487129173080987211241491021476555,21995817⟩,⟨-1884986293949054143909629636805085197511537940329092355420607751710538308515229,13262870⟩,⟨372279741837711207494205237704391182012323615603351099389950503022401518631716844,31944349⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0450_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0450_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0450_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0009
