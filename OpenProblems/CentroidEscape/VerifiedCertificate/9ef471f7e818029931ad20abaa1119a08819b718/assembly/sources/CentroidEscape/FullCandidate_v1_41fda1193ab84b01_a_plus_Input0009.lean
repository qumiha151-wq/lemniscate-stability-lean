import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0450_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0009
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0450_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0450_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0450_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0450_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0450_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨114966423123230619283969255310488235694999214042358114543315599488868865119154237,22989576⟩,⟨219692132293261511725492085142892307763459122019208475292388975495626208968329573,22333408⟩,⟨-22820314836351215293365808740404417311587484085614606231659313667186825634461145,16504864⟩,⟨10209467702569444240350693747033247444188966682484663910410694125135497534323576,16614805⟩,⟨11993138805003814495215283283732611008212107817328406236296338249929916006379454,5558955⟩,⟨-1969207534028157925215882925697911402412786626839197364927089666903792100316285,4265637⟩,⟨326980662634848545404170155369985280551634603993730803455672098752094996675445342,8033844⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨66304059056005778160898203704348155932508724041257006084195429967351824981974984,83208687⟩,⟨219495832606138616518443850519413634222321023383007077325845792784973164447442022,95010155⟩,⟨-23280626183597060898743096456171621991626984198277338126825590310447621164853501,49384951⟩,⟨-9111116534191347249118546847540502599260262979120828226825675473807214679518571,63801967⟩,⟨7903812749146811477189980682525375442703853992335127759148116210156088307228978,21995817⟩,⟨-1884986293949054143909629897864529818164846574446324426244498232654013312437636,13262870⟩,⟨372279741837711207494205317684004289367877267463113871681861440166263640686212140,31944349⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0450_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0450_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0450_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0009
