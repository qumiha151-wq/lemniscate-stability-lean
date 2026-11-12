import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0050_n0050_bounded_Step0070
import CentroidEscape.Shard_a_plus_s0050_n0050_bounded_Step0071
import CentroidEscape.Shard_a_plus_s0050_n0050_bounded_Step0072
import CentroidEscape.Shard_a_plus_s0050_n0050_bounded_Step0073
import CentroidEscape.Shard_a_plus_s0050_n0050_bounded_Step0074

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0050_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0071.inputData=Step0070.endpointData := by decide +kernel

theorem glue1 : Step0072.inputData=Step0071.endpointData := by decide +kernel

theorem glue2 : Step0073.inputData=Step0072.endpointData := by decide +kernel

theorem glue3 : Step0074.inputData=Step0073.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0070.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0074.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0070.stepData
  | 1=>Step0071.stepData
  | 2=>Step0072.stepData
  | 3=>Step0073.stepData
  | 4=>Step0074.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0070.stepData=true ∧
      (∀ i : Fin 7, Step0071.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0070.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0070.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0070.allStagesChecked,?_,Step0070.initialMarginCheck⟩
    intro i
    rw [Step0071.inputCoefficient,← Step0070.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0071.stepData=true ∧
      (∀ i : Fin 7, Step0072.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0071.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0071.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0071.allStagesChecked,?_,Step0071.initialMarginCheck⟩
    intro i
    rw [Step0072.inputCoefficient,← Step0071.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0072.stepData=true ∧
      (∀ i : Fin 7, Step0073.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0072.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0072.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0072.allStagesChecked,?_,Step0072.initialMarginCheck⟩
    intro i
    rw [Step0073.inputCoefficient,← Step0072.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0073.stepData=true ∧
      (∀ i : Fin 7, Step0074.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0073.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0073.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0073.allStagesChecked,?_,Step0073.initialMarginCheck⟩
    intro i
    rw [Step0074.inputCoefficient,← Step0073.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0074.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0074.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0074.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0074.allStagesChecked,?_,Step0074.initialMarginCheck⟩
    intro i
    change Step0074.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0074.stepData)[i.val]
    rw [← Step0074.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0070.stepData.coefficient 0 i=Step0070.inputData[i.val]
  exact Step0070.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0050_n0050_bounded.Block0004
