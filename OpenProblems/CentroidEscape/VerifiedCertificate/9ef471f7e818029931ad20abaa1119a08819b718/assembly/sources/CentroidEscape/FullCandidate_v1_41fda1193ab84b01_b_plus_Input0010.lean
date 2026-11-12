import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0010
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨66304059056005778160898171272932311405340089712996460954485145667789353370720657,83208687⟩,⟨219495832606138616518443829789472816906340830378919017114736102507747335904273786,95010155⟩,⟨-23280626183597060898743094115761536320349269234082880498104800030115584586953522,49384951⟩,⟨-9111116534191347249118552827730978306888332540866984202158073359537577348471361,63801967⟩,⟨7903812749146811477189977430874863998651871371922019103872877629596827457054162,21995817⟩,⟨-1884986293949054143909630243600531865247187268621112076056239262767005447498381,13262870⟩,⟨372279741837711207494205279207642425528741148924419262478204335487501655551701952,31944349⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨26736910545751401122118659044020550697033716265598108255409679996204253414355167,268165274⟩,⟨189833421115364391791242035555383324733246554877909619230510235526186970289208708,317144128⟩,⟨-16079676781181817823612626465741563049611600514885803513102403939956566020309283,153404436⟩,⟨-19142726937735969658051479844452397232875754956971512155514625893907315661979729,170122583⟩,⟨4808258784367743584213499537317289730407765846548409476144610373045027201421869,63510176⟩,⟨-1216558598236854029802892861755586294037999898066630322186785270127254378849807,29708966⟩,⟨394914536411609456520584280768759331218143401666702176068620282912270390884725212,111171861⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0010
