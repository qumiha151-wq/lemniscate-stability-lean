import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0250_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0005
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0250_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0250_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0250_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0250_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0250_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨24938191763066988911274374964894028886640940495039589453714352373355395288104019,202088⟩,⟨117631405237039638852881391632769392336573262875315882126592254696376569283992687,202481⟩,⟨23928826971836269647780384150821022308942720578583537259384953496329213212807843,141740⟩,⟨7239560743023091850147921794765994777003190200595546417532963867322885958023289,152753⟩,⟨-7728473027173560121659920755542402927789476058676345489395276171197833759419872,51426⟩,⟨5379623488340696238452471051752358679800984359467707436157724225251638509283837,32458⟩,⟨118760977850279989361174368703321854092842271200310552656985982236980685804719353,61653⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨74410945529556449893728900192686445723177056786910013336615846892028430466776839,579251⟩,⟨123830848533827514136642820761954680110516079937814928426859007994896136701225270,719377⟩,⟨24897828455411095575254604406416510102944683659232762576149720353250064855566117,219753⟩,⟨2257905712141571856790978107433057644297968247647026986928543771759946026403943,379139⟩,⟨2369537029564904046541400829227130378140259917586076175420335674239625307826285,136892⟩,⟨4614159619900903858855781540286383919047974434109450678843402158540520728036778,52845⟩,⟨143518408348922581784737314868292501048478333132790684297402913855391410540134622,250918⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0250_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0250_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0250_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0005
