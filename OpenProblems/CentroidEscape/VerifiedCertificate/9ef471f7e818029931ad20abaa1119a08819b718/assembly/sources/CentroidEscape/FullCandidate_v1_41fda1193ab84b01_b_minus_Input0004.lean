import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0004
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-10399574578046393184984876810200534659374364394011503986658815627899632332377663,36963⟩,⟨85442865890865607693211181983059525651904627893749152543294938508978551146381206,41962⟩,⟨6486651728218895365908492268347323881702143186777278170306091796215382695236310,35480⟩,⟨24143805610483091735526023394560262648338222089291090176413939838065131144939452,31329⟩,⟨-16649182158820813916608381687058465063200838213615548939881793487617641936339475,10981⟩,⟨2274803329425741397091126842592730586514511099187837964913550914339106699861746,9335⟩,⟨116562527270403178336730984982859879684138440261751827464321035259959692763731447,10868⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨24938191763066988911274359594283807578087849464594208972176106627972514795583370,202088⟩,⟨117631405237039638852881392404799459029554974449586802729517602331001217663929458,202481⟩,⟨23928826971836269647780383176986154822068598131987975041122714500049206042879286,141740⟩,⟨7239560743023091850147925013569851860709807977671141461712096340385371129337279,152753⟩,⟨-7728473027173560121659922762812335831508665305191376969106526535489930662061591,51426⟩,⟨5379623488340696238452470511734045668912393174754714375176305409157379620718139,32458⟩,⟨118760977850279989361174361079172509342956005370607595138605804212581663536802985,61653⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0004
