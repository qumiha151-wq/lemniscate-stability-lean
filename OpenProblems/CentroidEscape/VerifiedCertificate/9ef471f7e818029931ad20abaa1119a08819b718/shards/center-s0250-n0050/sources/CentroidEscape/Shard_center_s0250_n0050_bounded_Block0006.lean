import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0250_n0050_bounded_Step0280
import CentroidEscape.Shard_center_s0250_n0050_bounded_Step0281
import CentroidEscape.Shard_center_s0250_n0050_bounded_Step0282
import CentroidEscape.Shard_center_s0250_n0050_bounded_Step0283
import CentroidEscape.Shard_center_s0250_n0050_bounded_Step0284

namespace CentroidEscape.CertificateShards.Shard_center_s0250_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0281.inputData=Step0280.endpointData := by decide +kernel

theorem glue1 : Step0282.inputData=Step0281.endpointData := by decide +kernel

theorem glue2 : Step0283.inputData=Step0282.endpointData := by decide +kernel

theorem glue3 : Step0284.inputData=Step0283.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0280.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0284.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0280.stepData
  | 1=>Step0281.stepData
  | 2=>Step0282.stepData
  | 3=>Step0283.stepData
  | 4=>Step0284.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0280.stepData=true ∧
      (∀ i : Fin 7, Step0281.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0280.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0280.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0280.allStagesChecked,?_,Step0280.initialMarginCheck⟩
    intro i
    rw [Step0281.inputCoefficient,← Step0280.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0281.stepData=true ∧
      (∀ i : Fin 7, Step0282.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0281.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0281.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0281.allStagesChecked,?_,Step0281.initialMarginCheck⟩
    intro i
    rw [Step0282.inputCoefficient,← Step0281.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0282.stepData=true ∧
      (∀ i : Fin 7, Step0283.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0282.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0282.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0282.allStagesChecked,?_,Step0282.initialMarginCheck⟩
    intro i
    rw [Step0283.inputCoefficient,← Step0282.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0283.stepData=true ∧
      (∀ i : Fin 7, Step0284.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0283.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0283.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0283.allStagesChecked,?_,Step0283.initialMarginCheck⟩
    intro i
    rw [Step0284.inputCoefficient,← Step0283.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0284.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0284.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0284.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0284.allStagesChecked,?_,Step0284.initialMarginCheck⟩
    intro i
    change Step0284.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0284.stepData)[i.val]
    rw [← Step0284.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0280.stepData.coefficient 0 i=Step0280.inputData[i.val]
  exact Step0280.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0250_n0050_bounded.Block0006
