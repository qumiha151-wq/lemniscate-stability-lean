import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0150_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0003
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨8183871769865510774356701746181034665748953304125179338858555701395144515404809,5831⟩,⟨42939300018697361417927489500442397936540775931996397801421641026861936071285000,10366⟩,⟨-21585906549119939751882167945615439628987136830077690542421066819955330392674133,4418⟩,⟨12611448705547705396324972999507535958301995792611396960537347090028849698842685,6726⟩,⟨-13505958509762750645695969050327811457981996321575156258504573791602458861001386,2536⟩,⟨-4864146522450628058538339411200611208550483620389743128493954259317019181869139,1338⟩,⟨119543235749626701466766882982198784931820013224253289158943685992765011725664036,2584⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-10399574578046393184984868005519170333446245918706120547198756892476879907897083,36963⟩,⟨85442865890865607693211187832460350760027710095809638316842727098205854403523687,41962⟩,⟨6486651728218895365908497798912863295498997224840383548740503271348515461768966,35480⟩,⟨24143805610483091735526021908677999800358176719330971236429103333050632317684143,31329⟩,⟨-16649182158820813916608381638137322340382408880496776325782573317572976080841682,10981⟩,⟨2274803329425741397091128215455497580209913521205992283917826248416973833316835,9335⟩,⟨116562527270403178336730986154264120013973063402855652857415565288181508075171571,10868⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0003
