import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0200_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0004
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-10399574578046393184984868005519170333446245918706120547198756892476879907897083,36963⟩,⟨85442865890865607693211187832460350760027710095809638316842727098205854403523687,41962⟩,⟨6486651728218895365908497798912863295498997224840383548740503271348515461768966,35480⟩,⟨24143805610483091735526021908677999800358176719330971236429103333050632317684143,31329⟩,⟨-16649182158820813916608381638137322340382408880496776325782573317572976080841682,10981⟩,⟨2274803329425741397091128215455497580209913521205992283917826248416973833316835,9335⟩,⟨116562527270403178336730986154264120013973063402855652857415565288181508075171571,10868⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨24938191763066988911274374964894028886640940495039589453714352373355395288104019,202088⟩,⟨117631405237039638852881391632769392336573262875315882126592254696376569283992687,202481⟩,⟨23928826971836269647780384150821022308942720578583537259384953496329213212807843,141740⟩,⟨7239560743023091850147921794765994777003190200595546417532963867322885958023289,152753⟩,⟨-7728473027173560121659920755542402927789476058676345489395276171197833759419872,51426⟩,⟨5379623488340696238452471051752358679800984359467707436157724225251638509283837,32458⟩,⟨118760977850279989361174368703321854092842271200310552656985982236980685804719353,61653⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0004
