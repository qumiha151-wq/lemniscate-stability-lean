import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨56847420197934352695064258327676642198142232177709690045188228170630864167247486,1852⟩,⟨36241857394904228192084573290573710227843703221556962504074965437677261348676133,2675⟩,⟨-24889095447257238081877467022270589046263686711956316134742461267217019571260666,915⟩,⟨-2352217638170206359536256273202532071311362333519660367035077713703462049012411,1975⟩,⟨-1633364461257674383022635387406863069141683907793319403381265234518878846350137,1036⟩,⟨-6360219202563342902211725591688079744703559472294557594566152220172320077255324,441⟩,⟨103513494586400497105262214287734602477658272405083416650123042254690596251220433,834⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨8183871769865510774356691861390467910417949769469385386814233065069122491347284,5831⟩,⟨42939300018697361417927490377983419792187337701797650517217708525415254984152618,10366⟩,⟨-21585906549119939751882167718365867786672477489041111899633817995529681428295164,4418⟩,⟨12611448705547705396324973388470623042648589571439638857693026629853991942110004,6726⟩,⟨-13505958509762750645695969172267307316045736852103627236703402619713588139202282,2536⟩,⟨-4864146522450628058538339392881046797914967682666719398056731915201389439013268,1338⟩,⟨119543235749626701466766868009509395763785504828254966529250500549669331032814833,2584⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002
