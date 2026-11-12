import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0200_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0004
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0200_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0200_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0200_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0200_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0200_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-10399574578046393184984859200837806007518127443399765545773291766363506215529694,36963⟩,⟨85442865890865607693211193681861175868150792297868843921429465310634788613635119,41962⟩,⟨6486651728218895365908503329478402709295851262902807634015016644228063362041512,35480⟩,⟨24143805610483091735526020422795736952378131349369677018184927282640942349235988,31329⟩,⟨-16649182158820813916608381589216179617563979547377552358262578547441763188179568,10981⟩,⟨2274803329425741397091129588318264573905315943224168643115923656317591218487789,9335⟩,⟨116562527270403178336730987325668360343807686543960032194664389063285997553915544,10868⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨24938191763066988911274390335504250195194031525483793162892317598347108739970187,202088⟩,⟨117631405237039638852881390860739325643591551301043462636366248550154942604503773,202481⟩,⟨23928826971836269647780385124655889795816843025178361152645867397493309195136984,141740⟩,⟨7239560743023091850147918575962137693296572423520829630863074117724300206989138,152753⟩,⟨-7728473027173560121659918748272470024070286812161097774122084684240760718546923,51426⟩,⟨5379623488340696238452471591770671690689575544180604844084437561906192116702596,32458⟩,⟨118760977850279989361174376327471198842728537030014009093361360523694002071634396,61653⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0200_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0200_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0200_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0004
