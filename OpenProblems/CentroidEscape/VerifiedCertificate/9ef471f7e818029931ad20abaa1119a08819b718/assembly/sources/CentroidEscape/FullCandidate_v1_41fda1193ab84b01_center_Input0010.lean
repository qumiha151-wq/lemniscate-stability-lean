import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0500_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0010
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨66304059056005778160898199348838676062045488305140496112951229290385603455532002,83208687⟩,⟨219495832606138616518443851890754554445855274603345807904722217550818184722889719,95010155⟩,⟨-23280626183597060898743096987219033163890550831894313134280122013029321578888898,49384951⟩,⟨-9111116534191347249118545490613915295356793051135784646491893636888127130690357,63801967⟩,⟨7903812749146811477189980730583695644012076723911165822428080472681071766715710,21995817⟩,⟨-1884986293949054143909629767334807507838192257387697568630322750863682442337653,13262870⟩,⟨372279741837711207494205277694197735690100441533232698799318185266849199736752836,31944349⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨26736910545751401122118682444757111647793746037148172710328021549197234437564945,268165274⟩,⟨189833421115364391791242064888055040120869183295573252160949953240942261080463157,317144128⟩,⟨-16079676781181817823612626960469194704356916957231523842836105126691431391418304,153404436⟩,⟨-19142726937735969658051479428886713325735799066584045319752964560071324362394332,170122583⟩,⟨4808258784367743584213503337788248946538974576679387872875726207820930879022236,63510176⟩,⟨-1216558598236854029802892808097564120961629955388499916973084951685063638226393,29708966⟩,⟨394914536411609456520584291906856035516869854588536260370880669005622446004030548,111171861⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0500_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0010
