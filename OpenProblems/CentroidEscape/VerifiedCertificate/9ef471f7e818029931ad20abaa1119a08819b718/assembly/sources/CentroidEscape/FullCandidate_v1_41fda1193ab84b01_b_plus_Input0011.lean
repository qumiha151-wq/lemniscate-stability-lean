import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0550_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0011
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨26736910545751401122118659044020550697033716265598108255409679996204253414355167,268165274⟩,⟨189833421115364391791242035555383324733246554877909619230510235526186970289208708,317144128⟩,⟨-16079676781181817823612626465741563049611600514885803513102403939956566020309283,153404436⟩,⟨-19142726937735969658051479844452397232875754956971512155514625893907315661979729,170122583⟩,⟨4808258784367743584213499537317289730407765846548409476144610373045027201421869,63510176⟩,⟨-1216558598236854029802892861755586294037999898066630322186785270127254378849807,29708966⟩,⟨394914536411609456520584280768759331218143401666702176068620282912270390884725212,111171861⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨1356659135563769418858489580999159753447214578336111921083052855643739590746502,793218604⟩,⟨147012205639035313396651685219191850341288000164740501379301083835663801856943423,822725352⟩,⟨-9656546163276567067638623888951853002600389837481147834430777818877544328079686,403649945⟩,⟨-23059729317503026841970164238993330327566442841936022883420714239901810610063634,347234376⟩,⟨2915638552065264640684029372864587903157783835954489745553953585379652546033466,147578542⟩,⟨-714866182853698828935138994604030556749119755060396382015740995493034857372547,56451754⟩,⟨401397796147287482688438040875264831861427167254722888777259566236589825632003924,355652033⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0550_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0011
