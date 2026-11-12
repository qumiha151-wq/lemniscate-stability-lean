import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0350_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0007
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0350_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0350_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0350_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0350_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0350_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨121553810172798882043011240775772509107031213005586329177858095082701509210022150,1341636⟩,⟨138465272571090522270758707164675655150746682326580510581982198523657947476598801,1966264⟩,⟨20342719032513784072609388369419094010514082608711451105632218779685171052577326,718204⟩,⟨14531819650828365992370091323714409142112835172464893469281584850213185880746171,994833⟩,⟨10450852538172521589435333982289357861014692062742674899247416711233158524981922,310477⟩,⟨3268022784248865384219360364756293941596785041955165393237347515210298663628165,156220⟩,⟨192826182191809906348007932833526416680581090672929130799163773441330409660194598,691846⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨142905810656662369708731376699883361339879440419014770605187205684143452753542154,5109983⟩,⟨181196357021159584207582892442874581404924486459884076828486360368911671999675302,5852881⟩,⟨-1866787428006226598546691413610506928837901007645184387769150200357204103379193,3869329⟩,⟨24930204666200353866364594055391940035834025025765768277522328134311105392319795,3432289⟩,⟨14166913131363564363366549623409972354881253984607503850784295194459340868781009,1142801⟩,⟨234456938532301383366708172984348866299150186368652038767327093989583495084438,880675⟩,⟨260779358711960011046503843417150962019041129253490025208096034516652521022994226,2050448⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0350_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0350_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0350_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0007
