import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0425
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0426
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0427
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0428
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0429

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0426.inputData=Step0425.endpointData := by decide +kernel

theorem glue1 : Step0427.inputData=Step0426.endpointData := by decide +kernel

theorem glue2 : Step0428.inputData=Step0427.endpointData := by decide +kernel

theorem glue3 : Step0429.inputData=Step0428.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0425.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0429.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0425.stepData
  | 1=>Step0426.stepData
  | 2=>Step0427.stepData
  | 3=>Step0428.stepData
  | 4=>Step0429.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0425.stepData=true ∧
      (∀ i : Fin 7, Step0426.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0425.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0425.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0425.allStagesChecked,?_,Step0425.initialMarginCheck⟩
    intro i
    rw [Step0426.inputCoefficient,← Step0425.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0426.stepData=true ∧
      (∀ i : Fin 7, Step0427.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0426.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0426.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0426.allStagesChecked,?_,Step0426.initialMarginCheck⟩
    intro i
    rw [Step0427.inputCoefficient,← Step0426.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0427.stepData=true ∧
      (∀ i : Fin 7, Step0428.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0427.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0427.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0427.allStagesChecked,?_,Step0427.initialMarginCheck⟩
    intro i
    rw [Step0428.inputCoefficient,← Step0427.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0428.stepData=true ∧
      (∀ i : Fin 7, Step0429.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0428.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0428.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0428.allStagesChecked,?_,Step0428.initialMarginCheck⟩
    intro i
    rw [Step0429.inputCoefficient,← Step0428.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0429.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0429.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0429.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0429.allStagesChecked,?_,Step0429.initialMarginCheck⟩
    intro i
    change Step0429.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0429.stepData)[i.val]
    rw [← Step0429.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0425.stepData.coefficient 0 i=Step0425.inputData[i.val]
  exact Step0425.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Block0005
