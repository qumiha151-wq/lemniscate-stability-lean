import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0115
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0116
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0117
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0118
import CentroidEscape.Shard_b_minus_s0100_n0050_bounded_Step0119

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0116.inputData=Step0115.endpointData := by decide +kernel

theorem glue1 : Step0117.inputData=Step0116.endpointData := by decide +kernel

theorem glue2 : Step0118.inputData=Step0117.endpointData := by decide +kernel

theorem glue3 : Step0119.inputData=Step0118.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0115.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0119.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0115.stepData
  | 1=>Step0116.stepData
  | 2=>Step0117.stepData
  | 3=>Step0118.stepData
  | 4=>Step0119.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0115.stepData=true ∧
      (∀ i : Fin 7, Step0116.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0115.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0115.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0115.allStagesChecked,?_,Step0115.initialMarginCheck⟩
    intro i
    rw [Step0116.inputCoefficient,← Step0115.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0116.stepData=true ∧
      (∀ i : Fin 7, Step0117.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0116.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0116.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0116.allStagesChecked,?_,Step0116.initialMarginCheck⟩
    intro i
    rw [Step0117.inputCoefficient,← Step0116.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0117.stepData=true ∧
      (∀ i : Fin 7, Step0118.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0117.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0117.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0117.allStagesChecked,?_,Step0117.initialMarginCheck⟩
    intro i
    rw [Step0118.inputCoefficient,← Step0117.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0118.stepData=true ∧
      (∀ i : Fin 7, Step0119.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0118.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0118.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0118.allStagesChecked,?_,Step0118.initialMarginCheck⟩
    intro i
    rw [Step0119.inputCoefficient,← Step0118.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0119.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0119.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0119.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0119.allStagesChecked,?_,Step0119.initialMarginCheck⟩
    intro i
    change Step0119.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0119.stepData)[i.val]
    rw [← Step0119.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0115.stepData.coefficient 0 i=Step0115.inputData[i.val]
  exact Step0115.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0100_n0050_bounded.Block0003
