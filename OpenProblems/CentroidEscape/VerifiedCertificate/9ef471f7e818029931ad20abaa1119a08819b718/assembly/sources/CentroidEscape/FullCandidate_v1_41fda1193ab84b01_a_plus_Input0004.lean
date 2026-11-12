import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0200_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0004
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0200_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0200_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0200_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0200_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0200_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-10399574578046393184984859068624079492621963987053069638672778651142525315668865,36963⟩,⟨85442865890865607693211186578981733793327705281543181785761705731386569150694708,41962⟩,⟨6486651728218895365908497204528935542588776180004141514058724517296276387715486,35480⟩,⟨24143805610483091735526022068369541158274389078262854626335486411209851724061278,31329⟩,⟨-16649182158820813916608381607357277620095010178150674918282505051386369920001376,10981⟩,⟨2274803329425741397091128164253830491487190729101740146590408199858804202480210,9335⟩,⟨116562527270403178336731005862886072450377033479974337643297567101702317817218849,10868⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨24938191763066988911274383100257442925956338981125081678938087478178822995340771,202088⟩,⟨117631405237039638852881391258342721943294144422893005146428404385003633485056044,202481⟩,⟨23928826971836269647780383972700303145562102999887281848700852717566064200019783,141740⟩,⟨7239560743023091850147922383506115932442265418960875863999615081299894533252263,152753⟩,⟨-7728473027173560121659920766329718262967607939587984316885499621034112412523173,51426⟩,⟨5379623488340696238452471058082949579297438334119660189737439303299067899727004,32458⟩,⟨118760977850279989361174392639845693213861786104678138068929529577462002349665959,61653⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0200_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0200_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0200_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0004
