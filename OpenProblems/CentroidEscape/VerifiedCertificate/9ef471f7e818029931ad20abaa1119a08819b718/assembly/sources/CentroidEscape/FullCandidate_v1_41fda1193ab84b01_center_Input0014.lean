import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_center_s0700_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0014
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_center_s0700_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_center_s0700_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0700_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_center_s0700_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_center_s0700_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-20558179781793703033934927228287121759406470587478326833022663671327776214642926,4677855090⟩,⟨49900539377603756958294509496262441652356318327817714207301616621442198670636569,3184444018⟩,⟨-2269715638730426298398462349041817819048469614642323022929839720783145043532258,1818534894⟩,⟨-24896754626242002085746969511775457790042814342284775433805977965038186089864973,860296857⟩,⟨1256363397232375782837151631070246903329551888378599924681792554410535517809636,560720234⟩,⟨-181038345466120966657406806957580275378565125504971601334157486452684882713767,165417359⟩,⟨389377527345019154378528545008244413310246996940404472340326304240571782484139924,2627785259⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-22768860997835500478084537365798073198359685204045980462006179551413585271766829,9766386938⟩,⟨377,5195505656⟩,⟨-504,3413993283⟩,⟨-25000000000000000000000000000000000000000000000000000000000000000000000000000080,1153707288⟩,⟨1078121152389093060191864034094951325154573603477313072631887123352854612306086,974734987⟩,⟨133,251216856⟩,⟨378365096320749419634974942366049493295828418426801828129183182587266106254116773,6104148048⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_center_s0700_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0700_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_center_s0700_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Input0014
