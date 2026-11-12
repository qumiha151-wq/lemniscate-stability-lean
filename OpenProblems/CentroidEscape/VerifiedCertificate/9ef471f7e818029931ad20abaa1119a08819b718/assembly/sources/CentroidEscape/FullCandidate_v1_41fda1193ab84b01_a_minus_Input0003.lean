import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨8183871769865510774356691861390467910417949769469385386814233065069122491347284,5831⟩,⟨42939300018697361417927490377983419792187337701797650517217708525415254984152618,10366⟩,⟨-21585906549119939751882167718365867786672477489041111899633817995529681428295164,4418⟩,⟨12611448705547705396324973388470623042648589571439638857693026629853991942110004,6726⟩,⟨-13505958509762750645695969172267307316045736852103627236703402619713588139202282,2536⟩,⟨-4864146522450628058538339392881046797914967682666719398056731915201389439013268,1338⟩,⟨119543235749626701466766868009509395763785504828254966529250500549669331032814833,2584⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-10399574578046393184984876942414261174270527850359136125713570273481055861689194,36963⟩,⟨85442865890865607693211189085938967726727714910076083559535134735121015379625352,41962⟩,⟨6486651728218895365908498393296791048409218269676633660687299734451007646488762,35480⟩,⟨24143805610483091735526021748986458442441964360399069987364392231031592846800835,31329⟩,⟨-16649182158820813916608381668917367060669807582842879362448201481284402598695348,10981⟩,⟨2274803329425741397091128266657164668932636313310247390005338275173129671863423,9335⟩,⟨116562527270403178336730966445642167577569093325736982319173808277112645498134882,10868⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003
