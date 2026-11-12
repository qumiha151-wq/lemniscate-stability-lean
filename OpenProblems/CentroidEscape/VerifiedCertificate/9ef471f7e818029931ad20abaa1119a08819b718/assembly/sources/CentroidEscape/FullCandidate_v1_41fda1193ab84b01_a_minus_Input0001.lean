import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0001
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨106470679385259113411467345238362208253455742035212269001869507797545154985420435,390⟩,⟨35694138938034160032058600712357886455140672886984706222179275072583352208874884,389⟩,⟨-23969828322878252131987103969821145750928908710417058503660037705148293524622072,374⟩,⟨7102628398821351730826628048081443740933445375753505192047258628880535830545645,422⟩,⟨11174926312489208776030326659900893259433396338918135670172056734809231196445809,265⟩,⟨-6179879857098116913936352920572370667244344194189351772217240555559946596282517,216⟩,⟨62675262137764506423514944011213718483680344028870508857606562233698443513306206,204⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨56847420197934352695064258327676642198142232177709690045188228170630864167247486,1852⟩,⟨36241857394904228192084573290573710227843703221556962504074965437677261348676133,2675⟩,⟨-24889095447257238081877467022270589046263686711956316134742461267217019571260666,915⟩,⟨-2352217638170206359536256273202532071311362333519660367035077713703462049012411,1975⟩,⟨-1633364461257674383022635387406863069141683907793319403381265234518878846350137,1036⟩,⟨-6360219202563342902211725591688079744703559472294557594566152220172320077255324,441⟩,⟨103513494586400497105262214287734602477658272405083416650123042254690596251220433,834⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0001
