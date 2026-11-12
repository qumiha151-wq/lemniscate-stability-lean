import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0450_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0009
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨114966423123230619283969250982304453330857871172243627465973011569456620417075674,22989576⟩,⟨219692132293261511725492083729321451860913332785549987320027911465639815674546320,22333408⟩,⟨-22820314836351215293365808192814004510364233751533079899611844314187944175766022,16504864⟩,⟨10209467702569444240350694971013378979008621065390517814149695051968143141730304,16614805⟩,⟨11993138805003814495215283143913528465410705362524700848309745710081848941514989,5558955⟩,⟨-1969207534028157925215882869273699886462421749929164564128466707392185128721107,4265637⟩,⟨326980662634848545404170117457573277892693471783248133629973518402648625222470043,8033844⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨66304059056005778160898199348838676062045488305140496112951229290385603455532002,83208687⟩,⟨219495832606138616518443851890754554445855274603345807904722217550818184722889719,95010155⟩,⟨-23280626183597060898743096987219033163890550831894313134280122013029321578888898,49384951⟩,⟨-9111116534191347249118545490613915295356793051135784646491893636888127130690357,63801967⟩,⟨7903812749146811477189980730583695644012076723911165822428080472681071766715710,21995817⟩,⟨-1884986293949054143909629767334807507838192257387697568630322750863682442337653,13262870⟩,⟨372279741837711207494205277694197735690100441533232698799318185266849199736752836,31944349⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0009
