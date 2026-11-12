import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Step0330
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Step0331
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Step0332
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Step0333
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Step0334

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0331.inputData=Step0330.endpointData := by decide +kernel

theorem glue1 : Step0332.inputData=Step0331.endpointData := by decide +kernel

theorem glue2 : Step0333.inputData=Step0332.endpointData := by decide +kernel

theorem glue3 : Step0334.inputData=Step0333.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0330.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0334.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0330.stepData
  | 1=>Step0331.stepData
  | 2=>Step0332.stepData
  | 3=>Step0333.stepData
  | 4=>Step0334.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0330.stepData=true ∧
      (∀ i : Fin 7, Step0331.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0330.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0330.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0330.allStagesChecked,?_,Step0330.initialMarginCheck⟩
    intro i
    rw [Step0331.inputCoefficient,← Step0330.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0331.stepData=true ∧
      (∀ i : Fin 7, Step0332.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0331.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0331.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0331.allStagesChecked,?_,Step0331.initialMarginCheck⟩
    intro i
    rw [Step0332.inputCoefficient,← Step0331.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0332.stepData=true ∧
      (∀ i : Fin 7, Step0333.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0332.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0332.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0332.allStagesChecked,?_,Step0332.initialMarginCheck⟩
    intro i
    rw [Step0333.inputCoefficient,← Step0332.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0333.stepData=true ∧
      (∀ i : Fin 7, Step0334.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0333.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0333.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0333.allStagesChecked,?_,Step0333.initialMarginCheck⟩
    intro i
    rw [Step0334.inputCoefficient,← Step0333.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0334.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0334.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0334.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0334.allStagesChecked,?_,Step0334.initialMarginCheck⟩
    intro i
    change Step0334.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0334.stepData)[i.val]
    rw [← Step0334.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0330.stepData.coefficient 0 i=Step0330.inputData[i.val]
  exact Step0330.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.Block0006
