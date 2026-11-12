import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0001
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨106470679385259113411467355814010172602255877940290687182839522376643522598524383,390⟩,⟨35694138938034160032058601381001102629160723658866536803492751299563055271934247,389⟩,⟨-23969828322878252131987103787062467468343104145297428322292855863760010526387092,374⟩,⟨7102628398821351730826628664852292075991440155220754423530211689420881114059839,422⟩,⟨11174926312489208776030326828307738706061255666943714927722820194811031884684431,265⟩,⟨-6179879857098116913936352359826265296382188810271042769873392169577079585127190,216⟩,⟨62675262137764506423514949139141014615210588462403459848753034239874817362457679,204⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨56847420197934352695064268988989988827955219967308898665317712957255520099830496,1852⟩,⟨36241857394904228192084574186754366569701410433556015270547794582809178385278285,2675⟩,⟨-24889095447257238081877466951046602799994443088012925412139300344942398292522692,915⟩,⟨-2352217638170206359536257026832027510567753524911131370672422480889037052393095,1975⟩,⟨-1633364461257674383022634175235410830120263912836695658051224122705272898029182,1036⟩,⟨-6360219202563342902211725089792259022884116144969626212055312298356759230238229,441⟩,⟨103513494586400497105262224728082366231447334813332929200846515143410081235350415,834⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0001
