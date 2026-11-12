import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0011
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨26736910545751401122118676560595164763488930352638609923017945249251934307410754,268165274⟩,⟨189833421115364391791242068352630722267248240297114090854968281246709133681608413,317144128⟩,⟨-16079676781181817823612627766296390035852130348641371728936131165351649183064800,153404436⟩,⟨-19142726937735969658051478752000871273955531020502946936242825670719633066378684,170122583⟩,⟨4808258784367743584213503718307607328289025439990063025245147696284091342383642,63510176⟩,⟨-1216558598236854029802892607283374239716044427596804304935536743882294524578906,29708966⟩,⟨394914536411609456520584249382111079095668612458006113634988438780448127224206922,111171861⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨1356659135563769418858511758068571204484494564831692057434953161430794910497919,793218604⟩,⟨147012205639035313396651715756728719809133004564007184771879898193605335401086181,822725352⟩,⟨-9656546163276567067638617498889813348208753694045589685091703578492121976701111,403649945⟩,⟨-23059729317503026841970166914910650193381062093864740430135444093969229554865408,347234376⟩,⟨2915638552065264640684033687093992366349460847423255244911081156188388896526214,147578542⟩,⟨-714866182853698828935139153594421888134143812554333705739280585891167025866682,56451754⟩,⟨401397796147287482688438018758515585819071739281094871437903598700047180755465437,355652033⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0011
