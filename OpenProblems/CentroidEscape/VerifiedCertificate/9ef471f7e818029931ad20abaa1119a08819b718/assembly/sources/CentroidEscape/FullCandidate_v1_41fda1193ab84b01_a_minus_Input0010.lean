import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0500_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0010
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0500_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0500_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0500_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0500_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0500_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨66304059056005778160898194993329196191582252569023696152505817039482180927615184,83208687⟩,⟨219495832606138616518443853262095474669389525823684117635559428345140226439761225,95010155⟩,⟨-23280626183597060898743097518266444336154117465511191378265327981626606599725064,49384951⟩,⟨-9111116534191347249118544133687327991453323123150755274410291386655747321966801,63801967⟩,⟨7903812749146811477189980778642015845320299455487129173080987211241491021476555,21995817⟩,⟨-1884986293949054143909629636805085197511537940329092355420607751710538308515229,13262870⟩,⟨372279741837711207494205237704391182012323615603351099389950503022401518631716844,31944349⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨26736910545751401122118676560595164763488930352638609923017945249251934307410754,268165274⟩,⟨189833421115364391791242068352630722267248240297114090854968281246709133681608413,317144128⟩,⟨-16079676781181817823612627766296390035852130348641371728936131165351649183064800,153404436⟩,⟨-19142726937735969658051478752000871273955531020502946936242825670719633066378684,170122583⟩,⟨4808258784367743584213503718307607328289025439990063025245147696284091342383642,63510176⟩,⟨-1216558598236854029802892607283374239716044427596804304935536743882294524578906,29708966⟩,⟨394914536411609456520584249382111079095668612458006113634988438780448127224206922,111171861⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0500_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0500_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0500_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0010
