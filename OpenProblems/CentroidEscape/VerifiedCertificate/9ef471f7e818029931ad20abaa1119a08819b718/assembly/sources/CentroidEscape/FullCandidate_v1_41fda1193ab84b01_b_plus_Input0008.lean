import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0008
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨142905810656662369708731364215193541651479594777612140241610433004081637510963701,5109983⟩,⟨181196357021159584207582903764970755729771380394623884349453078165985727270156779,5852881⟩,⟨-1866787428006226598546703606562562122469610902604302389556912047959107064346836,3869329⟩,⟨24930204666200353866364593142376988426642597955381598593626393606825303767856807,3432289⟩,⟨14166913131363564363366551001420644729931166000225499156367890533698443124593364,1142801⟩,⟨234456938532301383366706586900299944619402260992667399161934034780536287887879,880675⟩,⟨260779358711960011046503833317791430064292229889552650069590841815440066492227531,2050448⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨114966423123230619283969223500192213745953564297481851117847546647297207360260011,22989576⟩,⟨219692132293261511725492082550815520496520610332360609912727262947740438326793834,22333408⟩,⟨-22820314836351215293365813526691384185007100064459457939947488921941845655627320,16504864⟩,⟨10209467702569444240350683048671818308455257226105085023172239664213711814054633,16614805⟩,⟨11993138805003814495215281532114142308796883697095670417013909390363498047358085,5558955⟩,⟨-1969207534028157925215884157827899725603374230425241191480571720588139322329448,4265637⟩,⟨326980662634848545404170133545468150123524197023428726094048402600893605268737840,8033844⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0008
