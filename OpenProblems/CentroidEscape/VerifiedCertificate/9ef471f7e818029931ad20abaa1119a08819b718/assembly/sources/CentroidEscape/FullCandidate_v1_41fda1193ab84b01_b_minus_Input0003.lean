import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0003
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨8183871769865510774356701573766127578440254945206310800576664982852118541809793,5831⟩,⟨42939300018697361417927486908965862464717296369175788497665939904228642841076471,10366⟩,⟨-21585906549119939751882169748401343792336352497785768934988778393485250971701846,4418⟩,⟨12611448705547705396324969913837605094422402993223461677948157629623032154132983,6726⟩,⟨-13505958509762750645695967310618428748413927298503926181617713725268642132950433,2536⟩,⟨-4864146522450628058538339519065099036174134312598335170932103930803034547475068,1338⟩,⟨119543235749626701466766883702755697281705106458744545282750782016975732294211182,2584⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-10399574578046393184984876810200534659374364394011503986658815627899632332377663,36963⟩,⟨85442865890865607693211181983059525651904627893749152543294938508978551146381206,41962⟩,⟨6486651728218895365908492268347323881702143186777278170306091796215382695236310,35480⟩,⟨24143805610483091735526023394560262648338222089291090176413939838065131144939452,31329⟩,⟨-16649182158820813916608381687058465063200838213615548939881793487617641936339475,10981⟩,⟨2274803329425741397091126842592730586514511099187837964913550914339106699861746,9335⟩,⟨116562527270403178336730984982859879684138440261751827464321035259959692763731447,10868⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0003
