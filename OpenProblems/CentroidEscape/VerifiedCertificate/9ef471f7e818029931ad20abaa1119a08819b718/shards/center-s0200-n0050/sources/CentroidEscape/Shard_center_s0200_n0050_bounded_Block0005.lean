import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0225
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0226
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0227
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0228
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0229

namespace CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0226.inputData=Step0225.endpointData := by decide +kernel

theorem glue1 : Step0227.inputData=Step0226.endpointData := by decide +kernel

theorem glue2 : Step0228.inputData=Step0227.endpointData := by decide +kernel

theorem glue3 : Step0229.inputData=Step0228.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0225.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0229.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0225.stepData
  | 1=>Step0226.stepData
  | 2=>Step0227.stepData
  | 3=>Step0228.stepData
  | 4=>Step0229.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0225.stepData=true ∧
      (∀ i : Fin 7, Step0226.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0225.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0225.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0225.allStagesChecked,?_,Step0225.initialMarginCheck⟩
    intro i
    rw [Step0226.inputCoefficient,← Step0225.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0226.stepData=true ∧
      (∀ i : Fin 7, Step0227.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0226.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0226.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0226.allStagesChecked,?_,Step0226.initialMarginCheck⟩
    intro i
    rw [Step0227.inputCoefficient,← Step0226.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0227.stepData=true ∧
      (∀ i : Fin 7, Step0228.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0227.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0227.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0227.allStagesChecked,?_,Step0227.initialMarginCheck⟩
    intro i
    rw [Step0228.inputCoefficient,← Step0227.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0228.stepData=true ∧
      (∀ i : Fin 7, Step0229.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0228.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0228.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0228.allStagesChecked,?_,Step0228.initialMarginCheck⟩
    intro i
    rw [Step0229.inputCoefficient,← Step0228.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0229.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0229.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0229.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0229.allStagesChecked,?_,Step0229.initialMarginCheck⟩
    intro i
    change Step0229.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0229.stepData)[i.val]
    rw [← Step0229.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0225.stepData.coefficient 0 i=Step0225.inputData[i.val]
  exact Step0225.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Block0005
