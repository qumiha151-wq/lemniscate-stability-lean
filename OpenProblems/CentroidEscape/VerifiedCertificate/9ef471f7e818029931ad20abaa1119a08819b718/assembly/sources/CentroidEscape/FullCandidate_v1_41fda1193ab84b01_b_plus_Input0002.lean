import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0100_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0002
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨56847420197934352695064267660965446184493015455525982838426592614291413986063853,1852⟩,⟨36241857394904228192084571900792362769490729968446528926316549436424762981787089,2675⟩,⟨-24889095447257238081877467054520984480600375560394458463991600090473837634100662,915⟩,⟨-2352217638170206359536255931957250532906036140459595537656223184213663038935151,1975⟩,⟨-1633364461257674383022636381931194184844738141406373658528786359883243391756369,1036⟩,⟨-6360219202563342902211726051675160014863715068407078554243073988500109592244039,441⟩,⟨103513494586400497105262223818410828271624851675548428596765248835198187779971260,834⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨8183871769865510774356701918595941753057651663044486629720813393149470780549326,5831⟩,⟨42939300018697361417927492091918933408364255494817394040941491440072221637415420,10366⟩,⟨-21585906549119939751882166142829535465637921162369068932050149374978705190148259,4418⟩,⟨12611448705547705396324976085177466822181588591999249338519216737397937327781623,6726⟩,⟨-13505958509762750645695970790037194167550065344646338985294866011640039399940549,2536⟩,⟨-4864146522450628058538339303336123380926832928180964384801437465415796913149550,1338⟩,⟨119543235749626701466766882261641872581934919989762126629510622126614576777801830,2584⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0100_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0002
