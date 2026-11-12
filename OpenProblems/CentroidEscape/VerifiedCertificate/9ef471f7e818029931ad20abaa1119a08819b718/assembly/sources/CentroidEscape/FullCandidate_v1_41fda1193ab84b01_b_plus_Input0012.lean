import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0600_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0012
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0600_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0600_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0600_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0600_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0600_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨1356659135563769418858489580999159753447214578336111921083052855643739590746502,793218604⟩,⟨147012205639035313396651685219191850341288000164740501379301083835663801856943423,822725352⟩,⟨-9656546163276567067638623888951853002600389837481147834430777818877544328079686,403649945⟩,⟨-23059729317503026841970164238993330327566442841936022883420714239901810610063634,347234376⟩,⟨2915638552065264640684029372864587903157783835954489745553953585379652546033466,147578542⟩,⟨-714866182853698828935138994604030556749119755060396382015740995493034857372547,56451754⟩,⟨401397796147287482688438040875264831861427167254722888777259566236589825632003924,355652033⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-13229562225337410659321299852691826306406663470898744822012836578141780696608492,2046245006⟩,⟨99296444290087109208235334045662925767760876389168858667252757632560594642131280,1745321124⟩,⟨-5241552209031479160201729790258192506645502478204142154831979378076535968963758,903022527⟩,⟨-24444347617394030607981147857175580796412604002712897748149158326515352755099659,584361672⟩,⟨1825809130932201423522650714103105020872646105490943044703892249964896023464376,299893490⟩,⟨-398981586478450120082364577205147717017572502176220192122159236085410841445201,99503894⟩,⟨398065086162700116103319606289011937394508289755852954014481445909038109068906131,1023709769⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0600_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0600_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0600_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0012
