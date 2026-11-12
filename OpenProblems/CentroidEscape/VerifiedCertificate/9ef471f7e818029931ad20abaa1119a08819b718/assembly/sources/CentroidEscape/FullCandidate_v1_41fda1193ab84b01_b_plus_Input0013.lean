import CentroidEscape.CandidatePathAssembly
import CentroidEscape.Shard_b_plus_s0650_n0050_bounded_Audit

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0013
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem mesh_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0650_n0050_bounded.mesh=CandidateEndpointChecks.mesh := by decide +kernel
theorem time_matches : CentroidEscape.CertificateShards.Shard_b_plus_s0650_n0050_bounded.stepTime=CandidateEndpointChecks.parameters 2/750 := by decide +kernel
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0650_n0050_bounded.Merge003_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.CertificateShards.Shard_b_plus_s0650_n0050_bounded.Merge003_0000.endpointData
noncomputable def stages : ℕ → FixedTaylorState := CentroidEscape.CertificateShards.Shard_b_plus_s0650_n0050_bounded.Merge003_0000.stages
theorem input_literal : inputData=⟨#[⟨-13229562225337410659321299852691826306406663470898744822012836578141780696608492,2046245006⟩,⟨99296444290087109208235334045662925767760876389168858667252757632560594642131280,1745321124⟩,⟨-5241552209031479160201729790258192506645502478204142154831979378076535968963758,903022527⟩,⟨-24444347617394030607981147857175580796412604002712897748149158326515352755099659,584361672⟩,⟨1825809130932201423522650714103105020872646105490943044703892249964896023464376,299893490⟩,⟨-398981586478450120082364577205147717017572502176220192122159236085410841445201,99503894⟩,⟨398065086162700116103319606289011937394508289755852954014481445909038109068906131,1023709769⟩],rfl⟩ := by decide +kernel
theorem endpoint_literal : endpointData=⟨#[⟨-20558179781793703033935002236025925861080571086516061841727305780592554323527493,4677855090⟩,⟨49900539377603756958294492606588704622503387728860156328651034958885973436033793,3184444018⟩,⟨-2269715638730426298398476282585001501162052612904890829699164977217006550274063,1818534894⟩,⟨-24896754626242002085746968241522312683530003706967638924243474115740692763170630,860296857⟩,⟨1256363397232375782837152460996309752584890984848127957747331497943760379994246,560720234⟩,⟨-181038345466120966657404982755231872458664296332149356461854564651116578949254,165417359⟩,⟨389377527345019154378528472126144847224908226860274741564360054220585214338615150,2627785259⟩],rfl⟩ := by decide +kernel
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 50 stages := by
  have h := CentroidEscape.CertificateShards.Shard_b_plus_s0650_n0050_bounded.Merge003_0000.checked
  rw [mesh_matches,time_matches] at h
  exact h
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0650_n0050_bounded.Merge003_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] :=
  CentroidEscape.CertificateShards.Shard_b_plus_s0650_n0050_bounded.Merge003_0000.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Input0013
