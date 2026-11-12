import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0010
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨66304059056005778160898203704348155932508724041257006084195429967351824981974984,83208687⟩,⟨219495832606138616518443850519413634222321023383007077325845792784973164447442022,95010155⟩,⟨-23280626183597060898743096456171621991626984198277338126825590310447621164853501,49384951⟩,⟨-9111116534191347249118546847540502599260262979120828226825675473807214679518571,63801967⟩,⟨7903812749146811477189980682525375442703853992335127759148116210156088307228978,21995817⟩,⟨-1884986293949054143909629897864529818164846574446324426244498232654013312437636,13262870⟩,⟨372279741837711207494205317684004289367877267463113871681861440166263640686212140,31944349⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨26736910545751401122118688328919058532098561721657498625541746575740087201250620,268165274⟩,⟨189833421115364391791242061423479357974490126294032124531201201726777382138216889,317144128⟩,⟨-16079676781181817823612626154641999372861703565821752634226720439123480549172947,153404436⟩,⟨-19142726937735969658051480105772555377516067112665021438489363339759492925261522,170122583⟩,⟨4808258784367743584213502957268890564788923713368604862833322618570223343792674,63510176⟩,⟨-1216558598236854029802893008911754002207215483180207003790117396982360468380865,29708966⟩,⟨394914536411609456520584334431600991938071096719065863706053550624906983139820352,111171861⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Input0010
