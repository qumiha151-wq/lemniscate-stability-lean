import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0011
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨26736910545751401122118688328919058532098561721657498625541746575740087201250620,268165274⟩,⟨189833421115364391791242061423479357974490126294032124531201201726777382138216889,317144128⟩,⟨-16079676781181817823612626154641999372861703565821752634226720439123480549172947,153404436⟩,⟨-19142726937735969658051480105772555377516067112665021438489363339759492925261522,170122583⟩,⟨4808258784367743584213502957268890564788923713368604862833322618570223343792674,63510176⟩,⟨-1216558598236854029802893008911754002207215483180207003790117396982360468380865,29708966⟩,⟨394914536411609456520584334431600991938071096719065863706053550624906983139820352,111171861⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨1356659135563769418858525277348385806034760629435978040706786052046007654680894,793218604⟩,⟨147012205639035313396651707651733374603206578051260487987747148610411574191759084,822725352⟩,⟨-9656546163276567067638617768923750152754382389049235690021839992730213696517335,403649945⟩,⟨-23059729317503026841970166801830607470366137424907691529519477259217401073419693,347234376⟩,⟨2915638552065264640684032018411975475577720934408780953760123535957965028610167,147578542⟩,⟨-714866182853698828935139645773874566608154996453800366909051754511600607688747,56451754⟩,⟨401397796147287482688438110282408771528098707487737938289971298011577703799199150,355652033⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0011
