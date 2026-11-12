import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0009
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨114966423123230619283969223500192213745953564297481851117847546647297207360260011,22989576⟩,⟨219692132293261511725492082550815520496520610332360609912727262947740438326793834,22333408⟩,⟨-22820314836351215293365813526691384185007100064459457939947488921941845655627320,16504864⟩,⟨10209467702569444240350683048671818308455257226105085023172239664213711814054633,16614805⟩,⟨11993138805003814495215281532114142308796883697095670417013909390363498047358085,5558955⟩,⟨-1969207534028157925215884157827899725603374230425241191480571720588139322329448,4265637⟩,⟨326980662634848545404170133545468150123524197023428726094048402600893605268737840,8033844⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨66304059056005778160898171272932311405340089712996460954485145667789353370720657,83208687⟩,⟨219495832606138616518443829789472816906340830378919017114736102507747335904273786,95010155⟩,⟨-23280626183597060898743094115761536320349269234082880498104800030115584586953522,49384951⟩,⟨-9111116534191347249118552827730978306888332540866984202158073359537577348471361,63801967⟩,⟨7903812749146811477189977430874863998651871371922019103872877629596827457054162,21995817⟩,⟨-1884986293949054143909630243600531865247187268621112076056239262767005447498381,13262870⟩,⟨372279741837711207494205279207642425528741148924419262478204335487501655551701952,31944349⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0009
