import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0250_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0005
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0250_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0250_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0250_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0250_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0250_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨24938191763066988911274390335504250195194031525483793162892317598347108739970187,202088⟩,⟨117631405237039638852881390860739325643591551301043462636366248550154942604503773,202481⟩,⟨23928826971836269647780385124655889795816843025178361152645867397493309195136984,141740⟩,⟨7239560743023091850147918575962137693296572423520829630863074117724300206989138,152753⟩,⟨-7728473027173560121659918748272470024070286812161097774122084684240760718546923,51426⟩,⟨5379623488340696238452471591770671690689575544180604844084437561906192116702596,32458⟩,⟨118760977850279989361174376327471198842728537030014009093361360523694002071634396,61653⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨74410945529556449893728915983525344611011544215395841426675091328696482805785677,579251⟩,⟨123830848533827514136642817922454251171007906984414403646351808943317603282352189,719377⟩,⟨24897828455411095575254604269074039982285702219603970259499100259684369247519564,219753⟩,⟨2257905712141571856790979621902524778621378243341619497316333061940062168973840,379139⟩,⟨2369537029564904046541403672719816316481924554856649613938239561956907144334077,136892⟩,⟨4614159619900903858855781939567896392117629494489525212114336529019277682615673,52845⟩,⟨143518408348922581784737330355421830051892646090132898122701910405779833938092210,250918⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0250_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0250_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0250_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0005
