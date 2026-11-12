import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0004
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-10399574578046393184984876942414261174270527850359136125713570273481055861689194,36963⟩,⟨85442865890865607693211189085938967726727714910076083559535134735121015379625352,41962⟩,⟨6486651728218895365908498393296791048409218269676633660687299734451007646488762,35480⟩,⟨24143805610483091735526021748986458442441964360399069987364392231031592846800835,31329⟩,⟨-16649182158820813916608381668917367060669807582842879362448201481284402598695348,10981⟩,⟨2274803329425741397091128266657164668932636313310247390005338275173129671863423,9335⟩,⟨116562527270403178336730966445642167577569093325736982319173808277112645498134882,10868⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨24938191763066988911274366829530614847325542008954126276730787428498107171659635,202088⟩,⟨117631405237039638852881392007196062729852381327738711660301308687563449522802797,202481⟩,⟨23928826971836269647780384328941741472323338157279780632587853682912903105488779,141740⟩,⟨7239560743023091850147921206025873621564114982230204498055969488278792012404234,152753⟩,⟨-7728473027173560121659920744755087592611344177764700548909945535591890574093204,51426⟩,⟨5379623488340696238452471045421767780304530384815759311393945377700507413906343,32458⟩,⟨118760977850279989361174344766798014971822756295942999322379075682439220082819076,61653⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0004
