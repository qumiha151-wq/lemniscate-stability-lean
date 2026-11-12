import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0050_n0050_bounded_Step0080
import CentroidEscape.Shard_center_s0050_n0050_bounded_Step0081
import CentroidEscape.Shard_center_s0050_n0050_bounded_Step0082
import CentroidEscape.Shard_center_s0050_n0050_bounded_Step0083
import CentroidEscape.Shard_center_s0050_n0050_bounded_Step0084

namespace CentroidEscape.CertificateShards.Shard_center_s0050_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0081.inputData=Step0080.endpointData := by decide +kernel

theorem glue1 : Step0082.inputData=Step0081.endpointData := by decide +kernel

theorem glue2 : Step0083.inputData=Step0082.endpointData := by decide +kernel

theorem glue3 : Step0084.inputData=Step0083.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0080.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0084.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0080.stepData
  | 1=>Step0081.stepData
  | 2=>Step0082.stepData
  | 3=>Step0083.stepData
  | 4=>Step0084.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0080.stepData=true ∧
      (∀ i : Fin 7, Step0081.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0080.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0080.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0080.allStagesChecked,?_,Step0080.initialMarginCheck⟩
    intro i
    rw [Step0081.inputCoefficient,← Step0080.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0081.stepData=true ∧
      (∀ i : Fin 7, Step0082.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0081.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0081.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0081.allStagesChecked,?_,Step0081.initialMarginCheck⟩
    intro i
    rw [Step0082.inputCoefficient,← Step0081.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0082.stepData=true ∧
      (∀ i : Fin 7, Step0083.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0082.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0082.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0082.allStagesChecked,?_,Step0082.initialMarginCheck⟩
    intro i
    rw [Step0083.inputCoefficient,← Step0082.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0083.stepData=true ∧
      (∀ i : Fin 7, Step0084.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0083.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0083.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0083.allStagesChecked,?_,Step0083.initialMarginCheck⟩
    intro i
    rw [Step0084.inputCoefficient,← Step0083.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0084.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0084.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0084.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0084.allStagesChecked,?_,Step0084.initialMarginCheck⟩
    intro i
    change Step0084.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0084.stepData)[i.val]
    rw [← Step0084.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0080.stepData.coefficient 0 i=Step0080.inputData[i.val]
  exact Step0080.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0050_n0050_bounded.Block0006
