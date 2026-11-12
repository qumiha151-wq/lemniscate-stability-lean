import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0550_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0011
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0550_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0550_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0550_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0550_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0550_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨26736910545751401122118682444757111647793746037148172710328021549197234437564945,268165274⟩,⟨189833421115364391791242064888055040120869183295573252160949953240942261080463157,317144128⟩,⟨-16079676781181817823612626960469194704356916957231523842836105126691431391418304,153404436⟩,⟨-19142726937735969658051479428886713325735799066584045319752964560071324362394332,170122583⟩,⟨4808258784367743584213503337788248946538974576679387872875726207820930879022236,63510176⟩,⟨-1216558598236854029802892808097564120961629955388499916973084951685063638226393,29708966⟩,⟨394914536411609456520584291906856035516869854588536260370880669005622446004030548,111171861⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨1356659135563769418858518517708478505259627597134162432953964542094264364202331,793218604⟩,⟨147012205639035313396651711704231047206169791307633845261664318641488385758379605,822725352⟩,⟨-9656546163276567067638617633906781750481568041547242417404292723855058746553068,403649945⟩,⟨-23059729317503026841970166858370628831873599759386287747138461682347212281853173,347234376⟩,⟨2915638552065264640684032852752983920963590890916078929268117090331077884169009,147578542⟩,⟨-714866182853698828935139399684148227371149404504065508370113732217961090467613,56451754⟩,⟨401397796147287482688438064520462178673585223384416776863678595693381262023748269,355652033⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0550_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0550_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0550_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0011
