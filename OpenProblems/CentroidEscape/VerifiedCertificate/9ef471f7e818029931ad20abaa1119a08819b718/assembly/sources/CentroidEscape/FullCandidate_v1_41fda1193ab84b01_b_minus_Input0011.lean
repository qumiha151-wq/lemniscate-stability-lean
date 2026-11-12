import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0550_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0011
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0550_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0550_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0550_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0550_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0550_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨26736910545751401122118705845493672598553775808701719405011861488583433741608556,268165274⟩,⟨189833421115364391791242094220726755508491811713246435910569385431917538040755299,317144128⟩,⟨-16079676781181817823612627455196826359102233399582983128442912923186054643618868,153404436⟩,⟨-19142726937735969658051479013321029418595843176191736017916866979160013728332425,170122583⟩,⟨4808258784367743584213507138259208162670183306810152338287867343300840755558650,63510176⟩,⟨-1216558598236854029802892754439541947885260012710225649993527222350039965858922,29708966⟩,⟨394914536411609456520584303044952739815596307510370036809915424581797104547570190,111171861⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨1356659135563769418858547454417797257072040615923076479746521295205300910170868,793218604⟩,⟨147012205639035313396651738189270244071051582450545534103209386348131001901120645,822725352⟩,⟨-9656546163276567067638611378861710498362746245619792581245120349536447166075352,403649945⟩,⟨-23059729317503026841970169477747927336180756676831855012743075020182545355147397,347234376⟩,⟨2915638552065264640684036332641379938769397945877574673407278189738107650343845,147578542⟩,⟨-714866182853698828935139804764265897993179053947732469339748083550612488222147,56451754⟩,⟨401397796147287482688438088165659525485743279514108997255506539556610418495964340,355652033⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0550_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0550_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0550_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0011
