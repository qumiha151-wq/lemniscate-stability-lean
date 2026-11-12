import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0005
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨24938191763066988911274366829530614847325542008954126276730787428498107171659635,202088⟩,⟨117631405237039638852881392007196062729852381327738711660301308687563449522802797,202481⟩,⟨23928826971836269647780384328941741472323338157279780632587853682912903105488779,141740⟩,⟨7239560743023091850147921206025873621564114982230204498055969488278792012404234,152753⟩,⟨-7728473027173560121659920744755087592611344177764700548909945535591890574093204,51426⟩,⟨5379623488340696238452471045421767780304530384815759311393945377700507413906343,32458⟩,⟨118760977850279989361174344766798014971822756295942999322379075682439220082819076,61653⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨74410945529556449893728892209246969019827351026543966489587176354335919352498428,579251⟩,⟨123830848533827514136642819923640197052484299172408687581811050198834550259976832,719377⟩,⟨24897828455411095575254604462619791375473479202558137750803187046153143649556578,219753⟩,⟨2257905712141571856790977487681910273578328981417748793823382352001334406144191,379139⟩,⟨2369537029564904046541400805435047406296368409945497858982669443532336932951850,136892⟩,⟨4614159619900903858855781515214326694106254664876147866526089780131871501153710,52845⟩,⟨143518408348922581784737286914853418804861720716249135744432928580948136660362427,250918⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0005
