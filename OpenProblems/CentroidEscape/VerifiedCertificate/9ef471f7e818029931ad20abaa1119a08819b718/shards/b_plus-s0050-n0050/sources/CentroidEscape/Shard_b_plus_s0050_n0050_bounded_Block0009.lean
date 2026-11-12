import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0050_n0050_bounded_Step0095
import CentroidEscape.Shard_b_plus_s0050_n0050_bounded_Step0096
import CentroidEscape.Shard_b_plus_s0050_n0050_bounded_Step0097
import CentroidEscape.Shard_b_plus_s0050_n0050_bounded_Step0098
import CentroidEscape.Shard_b_plus_s0050_n0050_bounded_Step0099

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0050_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0096.inputData=Step0095.endpointData := by decide +kernel

theorem glue1 : Step0097.inputData=Step0096.endpointData := by decide +kernel

theorem glue2 : Step0098.inputData=Step0097.endpointData := by decide +kernel

theorem glue3 : Step0099.inputData=Step0098.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0095.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0099.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0095.stepData
  | 1=>Step0096.stepData
  | 2=>Step0097.stepData
  | 3=>Step0098.stepData
  | 4=>Step0099.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0095.stepData=true ∧
      (∀ i : Fin 7, Step0096.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0095.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0095.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0095.allStagesChecked,?_,Step0095.initialMarginCheck⟩
    intro i
    rw [Step0096.inputCoefficient,← Step0095.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0096.stepData=true ∧
      (∀ i : Fin 7, Step0097.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0096.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0096.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0096.allStagesChecked,?_,Step0096.initialMarginCheck⟩
    intro i
    rw [Step0097.inputCoefficient,← Step0096.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0097.stepData=true ∧
      (∀ i : Fin 7, Step0098.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0097.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0097.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0097.allStagesChecked,?_,Step0097.initialMarginCheck⟩
    intro i
    rw [Step0098.inputCoefficient,← Step0097.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0098.stepData=true ∧
      (∀ i : Fin 7, Step0099.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0098.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0098.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0098.allStagesChecked,?_,Step0098.initialMarginCheck⟩
    intro i
    rw [Step0099.inputCoefficient,← Step0098.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0099.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0099.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0099.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0099.allStagesChecked,?_,Step0099.initialMarginCheck⟩
    intro i
    change Step0099.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0099.stepData)[i.val]
    rw [← Step0099.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0095.stepData.coefficient 0 i=Step0095.inputData[i.val]
  exact Step0095.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0050_n0050_bounded.Block0009
