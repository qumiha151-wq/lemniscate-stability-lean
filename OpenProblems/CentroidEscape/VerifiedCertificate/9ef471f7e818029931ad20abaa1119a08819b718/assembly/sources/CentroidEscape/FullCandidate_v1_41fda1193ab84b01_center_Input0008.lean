import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0400_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0008
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0400_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0400_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0400_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0400_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0400_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨142905810656662369708731370594015461684343529448809231305910670876662644265178597,5109983⟩,⟨181196357021159584207582889664815989123085729907151583683144837697577805520096392,5852881⟩,⟨-1866787428006226598546690413621721644249751705644123645708751704984080014388247,3869329⟩,⟨24930204666200353866364594130271649910313907829882000835293359474973458963385965,3432289⟩,⟨14166913131363564363366549451609246832483632224370128912919147218077487927315395,1142801⟩,⟨234456938532301383366708150801768587323533511314455348752530778313252623986997,880675⟩,⟨260779358711960011046503808072959834770431294107857313746822165072623381227590696,2050448⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨114966423123230619283969250982304453330857871172243627465973011569456620417075674,22989576⟩,⟨219692132293261511725492083729321451860913332785549987320027911465639815674546320,22333408⟩,⟨-22820314836351215293365808192814004510364233751533079899611844314187944175766022,16504864⟩,⟨10209467702569444240350694971013378979008621065390517814149695051968143141730304,16614805⟩,⟨11993138805003814495215283143913528465410705362524700848309745710081848941514989,5558955⟩,⟨-1969207534028157925215882869273699886462421749929164564128466707392185128721107,4265637⟩,⟨326980662634848545404170117457573277892693471783248133629973518402648625222470043,8033844⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0400_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0400_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0400_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0008
