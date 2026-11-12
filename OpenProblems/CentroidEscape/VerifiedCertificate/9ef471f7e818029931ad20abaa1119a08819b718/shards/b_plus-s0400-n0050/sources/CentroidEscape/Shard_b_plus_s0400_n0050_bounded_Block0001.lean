import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0405
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0406
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0407
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0408
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0409

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0406.inputData=Step0405.endpointData := by decide +kernel

theorem glue1 : Step0407.inputData=Step0406.endpointData := by decide +kernel

theorem glue2 : Step0408.inputData=Step0407.endpointData := by decide +kernel

theorem glue3 : Step0409.inputData=Step0408.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0405.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0409.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0405.stepData
  | 1=>Step0406.stepData
  | 2=>Step0407.stepData
  | 3=>Step0408.stepData
  | 4=>Step0409.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0405.stepData=true ∧
      (∀ i : Fin 7, Step0406.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0405.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0405.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0405.allStagesChecked,?_,Step0405.initialMarginCheck⟩
    intro i
    rw [Step0406.inputCoefficient,← Step0405.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0406.stepData=true ∧
      (∀ i : Fin 7, Step0407.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0406.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0406.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0406.allStagesChecked,?_,Step0406.initialMarginCheck⟩
    intro i
    rw [Step0407.inputCoefficient,← Step0406.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0407.stepData=true ∧
      (∀ i : Fin 7, Step0408.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0407.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0407.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0407.allStagesChecked,?_,Step0407.initialMarginCheck⟩
    intro i
    rw [Step0408.inputCoefficient,← Step0407.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0408.stepData=true ∧
      (∀ i : Fin 7, Step0409.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0408.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0408.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0408.allStagesChecked,?_,Step0408.initialMarginCheck⟩
    intro i
    rw [Step0409.inputCoefficient,← Step0408.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0409.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0409.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0409.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0409.allStagesChecked,?_,Step0409.initialMarginCheck⟩
    intro i
    change Step0409.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0409.stepData)[i.val]
    rw [← Step0409.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0405.stepData.coefficient 0 i=Step0405.inputData[i.val]
  exact Step0405.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Block0001
