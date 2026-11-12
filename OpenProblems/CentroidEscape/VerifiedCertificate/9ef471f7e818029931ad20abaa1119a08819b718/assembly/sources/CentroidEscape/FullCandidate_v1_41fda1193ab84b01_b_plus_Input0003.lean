import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0150_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0003
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0150_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0150_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0150_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0150_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0150_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨8183871769865510774356701918595941753057651663044486629720813393149470780549326,5831⟩,⟨42939300018697361417927492091918933408364255494817394040941491440072221637415420,10366⟩,⟨-21585906549119939751882166142829535465637921162369068932050149374978705190148259,4418⟩,⟨12611448705547705396324976085177466822181588591999249338519216737397937327781623,6726⟩,⟨-13505958509762750645695970790037194167550065344646338985294866011640039399940549,2536⟩,⟨-4864146522450628058538339303336123380926832928180964384801437465415796913149550,1338⟩,⟨119543235749626701466766882261641872581934919989762126629510622126614576777801830,2584⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-10399574578046393184984859200837806007518127443399765545773291766363506215529694,36963⟩,⟨85442865890865607693211193681861175868150792297868843921429465310634788613635119,41962⟩,⟨6486651728218895365908503329478402709295851262902807634015016644228063362041512,35480⟩,⟨24143805610483091735526020422795736952378131349369677018184927282640942349235988,31329⟩,⟨-16649182158820813916608381589216179617563979547377552358262578547441763188179568,10981⟩,⟨2274803329425741397091129588318264573905315943224168643115923656317591218487789,9335⟩,⟨116562527270403178336730987325668360343807686543960032194664389063285997553915544,10868⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0150_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0150_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0150_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0003
