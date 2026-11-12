import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0002
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨56847420197934352695064268988989988827955219967308898665317712957255520099830496,1852⟩,⟨36241857394904228192084574186754366569701410433556015270547794582809178385278285,2675⟩,⟨-24889095447257238081877466951046602799994443088012925412139300344942398292522692,915⟩,⟨-2352217638170206359536257026832027510567753524911131370672422480889037052393095,1975⟩,⟨-1633364461257674383022634175235410830120263912836695658051224122705272898029182,1036⟩,⟨-6360219202563342902211725089792259022884116144969626212055312298356759230238229,441⟩,⟨103513494586400497105262224728082366231447334813332929200846515143410081235350415,834⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨8183871769865510774356701573766127578440254945206310800576664982852118541809793,5831⟩,⟨42939300018697361417927486908965862464717296369175788497665939904228642841076471,10366⟩,⟨-21585906549119939751882169748401343792336352497785768934988778393485250971701846,4418⟩,⟨12611448705547705396324969913837605094422402993223461677948157629623032154132983,6726⟩,⟨-13505958509762750645695967310618428748413927298503926181617713725268642132950433,2536⟩,⟨-4864146522450628058538339519065099036174134312598335170932103930803034547475068,1338⟩,⟨119543235749626701466766883702755697281705106458744545282750782016975732294211182,2584⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0002
