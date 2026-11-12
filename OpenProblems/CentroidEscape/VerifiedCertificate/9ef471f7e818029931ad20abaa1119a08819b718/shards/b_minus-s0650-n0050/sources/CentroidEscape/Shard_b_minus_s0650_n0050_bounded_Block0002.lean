import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Step0660
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Step0661
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Step0662
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Step0663
import CentroidEscape.Shard_b_minus_s0650_n0050_bounded_Step0664

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0661.inputData=Step0660.endpointData := by decide +kernel

theorem glue1 : Step0662.inputData=Step0661.endpointData := by decide +kernel

theorem glue2 : Step0663.inputData=Step0662.endpointData := by decide +kernel

theorem glue3 : Step0664.inputData=Step0663.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0660.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0664.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0660.stepData
  | 1=>Step0661.stepData
  | 2=>Step0662.stepData
  | 3=>Step0663.stepData
  | 4=>Step0664.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0660.stepData=true ∧
      (∀ i : Fin 7, Step0661.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0660.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0660.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0660.allStagesChecked,?_,Step0660.initialMarginCheck⟩
    intro i
    rw [Step0661.inputCoefficient,← Step0660.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0661.stepData=true ∧
      (∀ i : Fin 7, Step0662.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0661.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0661.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0661.allStagesChecked,?_,Step0661.initialMarginCheck⟩
    intro i
    rw [Step0662.inputCoefficient,← Step0661.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0662.stepData=true ∧
      (∀ i : Fin 7, Step0663.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0662.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0662.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0662.allStagesChecked,?_,Step0662.initialMarginCheck⟩
    intro i
    rw [Step0663.inputCoefficient,← Step0662.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0663.stepData=true ∧
      (∀ i : Fin 7, Step0664.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0663.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0663.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0663.allStagesChecked,?_,Step0663.initialMarginCheck⟩
    intro i
    rw [Step0664.inputCoefficient,← Step0663.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0664.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0664.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0664.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0664.allStagesChecked,?_,Step0664.initialMarginCheck⟩
    intro i
    change Step0664.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0664.stepData)[i.val]
    rw [← Step0664.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0660.stepData.coefficient 0 i=Step0660.inputData[i.val]
  exact Step0660.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0650_n0050_bounded.Block0002
