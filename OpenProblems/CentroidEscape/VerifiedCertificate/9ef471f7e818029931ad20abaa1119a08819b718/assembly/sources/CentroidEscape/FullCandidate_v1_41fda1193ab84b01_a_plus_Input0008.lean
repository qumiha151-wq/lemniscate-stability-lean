import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0008
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨142905810656662369708731376699883361339879440419014770605187205684143452753542154,5109983⟩,⟨181196357021159584207582892442874581404924486459884076828486360368911671999675302,5852881⟩,⟨-1866787428006226598546691413610506928837901007645184387769150200357204103379193,3869329⟩,⟨24930204666200353866364594055391940035834025025765768277522328134311105392319795,3432289⟩,⟨14166913131363564363366549623409972354881253984607503850784295194459340868781009,1142801⟩,⟨234456938532301383366708172984348866299150186368652038767327093989583495084438,880675⟩,⟨260779358711960011046503843417150962019041129253490025208096034516652521022994226,2050448⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨114966423123230619283969255310488235694999214042358114543315599488868865119154237,22989576⟩,⟨219692132293261511725492085142892307763459122019208475292388975495626208968329573,22333408⟩,⟨-22820314836351215293365808740404417311587484085614606231659313667186825634461145,16504864⟩,⟨10209467702569444240350693747033247444188966682484663910410694125135497534323576,16614805⟩,⟨11993138805003814495215283283732611008212107817328406236296338249929916006379454,5558955⟩,⟨-1969207534028157925215882925697911402412786626839197364927089666903792100316285,4265637⟩,⟨326980662634848545404170155369985280551634603993730803455672098752094996675445342,8033844⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0008
