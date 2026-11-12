import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0355
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0356
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0357
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0358
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0359

namespace CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0356.inputData=Step0355.endpointData := by decide +kernel

theorem glue1 : Step0357.inputData=Step0356.endpointData := by decide +kernel

theorem glue2 : Step0358.inputData=Step0357.endpointData := by decide +kernel

theorem glue3 : Step0359.inputData=Step0358.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0355.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0359.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0355.stepData
  | 1=>Step0356.stepData
  | 2=>Step0357.stepData
  | 3=>Step0358.stepData
  | 4=>Step0359.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0355.stepData=true ∧
      (∀ i : Fin 7, Step0356.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0355.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0355.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0355.allStagesChecked,?_,Step0355.initialMarginCheck⟩
    intro i
    rw [Step0356.inputCoefficient,← Step0355.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0356.stepData=true ∧
      (∀ i : Fin 7, Step0357.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0356.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0356.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0356.allStagesChecked,?_,Step0356.initialMarginCheck⟩
    intro i
    rw [Step0357.inputCoefficient,← Step0356.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0357.stepData=true ∧
      (∀ i : Fin 7, Step0358.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0357.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0357.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0357.allStagesChecked,?_,Step0357.initialMarginCheck⟩
    intro i
    rw [Step0358.inputCoefficient,← Step0357.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0358.stepData=true ∧
      (∀ i : Fin 7, Step0359.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0358.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0358.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0358.allStagesChecked,?_,Step0358.initialMarginCheck⟩
    intro i
    rw [Step0359.inputCoefficient,← Step0358.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0359.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0359.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0359.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0359.allStagesChecked,?_,Step0359.initialMarginCheck⟩
    intro i
    change Step0359.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0359.stepData)[i.val]
    rw [← Step0359.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0355.stepData.coefficient 0 i=Step0355.inputData[i.val]
  exact Step0355.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Block0001
