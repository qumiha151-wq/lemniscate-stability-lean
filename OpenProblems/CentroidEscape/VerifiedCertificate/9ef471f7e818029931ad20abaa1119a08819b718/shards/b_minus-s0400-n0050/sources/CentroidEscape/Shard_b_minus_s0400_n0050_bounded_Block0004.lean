import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0420
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0421
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0422
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0423
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0424

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0421.inputData=Step0420.endpointData := by decide +kernel

theorem glue1 : Step0422.inputData=Step0421.endpointData := by decide +kernel

theorem glue2 : Step0423.inputData=Step0422.endpointData := by decide +kernel

theorem glue3 : Step0424.inputData=Step0423.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0420.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0424.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0420.stepData
  | 1=>Step0421.stepData
  | 2=>Step0422.stepData
  | 3=>Step0423.stepData
  | 4=>Step0424.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0420.stepData=true ∧
      (∀ i : Fin 7, Step0421.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0420.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0420.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0420.allStagesChecked,?_,Step0420.initialMarginCheck⟩
    intro i
    rw [Step0421.inputCoefficient,← Step0420.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0421.stepData=true ∧
      (∀ i : Fin 7, Step0422.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0421.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0421.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0421.allStagesChecked,?_,Step0421.initialMarginCheck⟩
    intro i
    rw [Step0422.inputCoefficient,← Step0421.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0422.stepData=true ∧
      (∀ i : Fin 7, Step0423.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0422.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0422.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0422.allStagesChecked,?_,Step0422.initialMarginCheck⟩
    intro i
    rw [Step0423.inputCoefficient,← Step0422.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0423.stepData=true ∧
      (∀ i : Fin 7, Step0424.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0423.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0423.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0423.allStagesChecked,?_,Step0423.initialMarginCheck⟩
    intro i
    rw [Step0424.inputCoefficient,← Step0423.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0424.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0424.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0424.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0424.allStagesChecked,?_,Step0424.initialMarginCheck⟩
    intro i
    change Step0424.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0424.stepData)[i.val]
    rw [← Step0424.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0420.stepData.coefficient 0 i=Step0420.inputData[i.val]
  exact Step0420.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Block0004
