import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0150_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0003
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0150_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0150_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0150_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0150_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0150_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨8183871769865510774356711630971601421079956838780984346501598454544095221412912,5831⟩,⟨42939300018697361417927488622901376080894214162195149402818511455318981523526820,10366⟩,⟨-21585906549119939751882168172865011471301796171114259269321720514606682469364949,4418⟩,⟨12611448705547705396324972610544448873955402013783155944228161621532321754276631,6726⟩,⟨-13505958509762750645695968928388315599918255791046688967675391067598865696715191,2536⟩,⟨-4864146522450628058538339429520175619185999558112767730297817005001115520366940,1338⟩,⟨119543235749626701466766897954888174099854521620251614346298403178436796586719643,2584⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-10399574578046393184984859068624079492621963987053069638672778651142525315668865,36963⟩,⟨85442865890865607693211186578981733793327705281543181785761705731386569150694708,41962⟩,⟨6486651728218895365908497204528935542588776180004141514058724517296276387715486,35480⟩,⟨24143805610483091735526022068369541158274389078262854626335486411209851724061278,31329⟩,⟨-16649182158820813916608381607357277620095010178150674918282505051386369920001376,10981⟩,⟨2274803329425741397091128164253830491487190729101740146590408199858804202480210,9335⟩,⟨116562527270403178336731005862886072450377033479974337643297567101702317817218849,10868⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0150_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0150_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0150_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0003
