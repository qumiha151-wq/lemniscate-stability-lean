import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0730
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0731
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0732
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0733
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0734

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0731.inputData=Step0730.endpointData := by decide +kernel

theorem glue1 : Step0732.inputData=Step0731.endpointData := by decide +kernel

theorem glue2 : Step0733.inputData=Step0732.endpointData := by decide +kernel

theorem glue3 : Step0734.inputData=Step0733.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0730.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0734.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0730.stepData
  | 1=>Step0731.stepData
  | 2=>Step0732.stepData
  | 3=>Step0733.stepData
  | 4=>Step0734.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0730.stepData=true ∧
      (∀ i : Fin 7, Step0731.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0730.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0730.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0730.allStagesChecked,?_,Step0730.initialMarginCheck⟩
    intro i
    rw [Step0731.inputCoefficient,← Step0730.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0731.stepData=true ∧
      (∀ i : Fin 7, Step0732.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0731.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0731.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0731.allStagesChecked,?_,Step0731.initialMarginCheck⟩
    intro i
    rw [Step0732.inputCoefficient,← Step0731.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0732.stepData=true ∧
      (∀ i : Fin 7, Step0733.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0732.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0732.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0732.allStagesChecked,?_,Step0732.initialMarginCheck⟩
    intro i
    rw [Step0733.inputCoefficient,← Step0732.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0733.stepData=true ∧
      (∀ i : Fin 7, Step0734.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0733.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0733.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0733.allStagesChecked,?_,Step0733.initialMarginCheck⟩
    intro i
    rw [Step0734.inputCoefficient,← Step0733.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0734.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0734.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0734.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0734.allStagesChecked,?_,Step0734.initialMarginCheck⟩
    intro i
    change Step0734.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0734.stepData)[i.val]
    rw [← Step0734.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0730.stepData.coefficient 0 i=Step0730.inputData[i.val]
  exact Step0730.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Block0006
