import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0100_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0002
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨56847420197934352695064268324977717506224117711417422852318679870834179366596774,1852⟩,⟨36241857394904228192084573043773364669596070201001200577362762764725861561610690,2675⟩,⟨-24889095447257238081877467002783793640297409324203692214534859362939062316228231,915⟩,⟨-2352217638170206359536256479394639021736894832685424801014104789009522288354686,1975⟩,⟨-1633364461257674383022635278583302507482501027121504520699517144311212139803425,1036⟩,⟨-6360219202563342902211725570733709518873915606688345323743319483162606266686710,441⟩,⟨103513494586400497105262224273246597251536093244440667916288066077222677447655497,834⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨8183871769865510774356701746181034665748953304125179338858555701395144515404809,5831⟩,⟨42939300018697361417927489500442397936540775931996397801421641026861936071285000,10366⟩,⟨-21585906549119939751882167945615439628987136830077690542421066819955330392674133,4418⟩,⟨12611448705547705396324972999507535958301995792611396960537347090028849698842685,6726⟩,⟨-13505958509762750645695969050327811457981996321575156258504573791602458861001386,2536⟩,⟨-4864146522450628058538339411200611208550483620389743128493954259317019181869139,1338⟩,⟨119543235749626701466766882982198784931820013224253289158943685992765011725664036,2584⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0002
