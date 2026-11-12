import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0450_n0050_bounded_Step0470
import CentroidEscape.Shard_center_s0450_n0050_bounded_Step0471
import CentroidEscape.Shard_center_s0450_n0050_bounded_Step0472
import CentroidEscape.Shard_center_s0450_n0050_bounded_Step0473
import CentroidEscape.Shard_center_s0450_n0050_bounded_Step0474

namespace CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0471.inputData=Step0470.endpointData := by decide +kernel

theorem glue1 : Step0472.inputData=Step0471.endpointData := by decide +kernel

theorem glue2 : Step0473.inputData=Step0472.endpointData := by decide +kernel

theorem glue3 : Step0474.inputData=Step0473.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0470.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0474.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0470.stepData
  | 1=>Step0471.stepData
  | 2=>Step0472.stepData
  | 3=>Step0473.stepData
  | 4=>Step0474.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0470.stepData=true ∧
      (∀ i : Fin 7, Step0471.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0470.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0470.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0470.allStagesChecked,?_,Step0470.initialMarginCheck⟩
    intro i
    rw [Step0471.inputCoefficient,← Step0470.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0471.stepData=true ∧
      (∀ i : Fin 7, Step0472.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0471.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0471.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0471.allStagesChecked,?_,Step0471.initialMarginCheck⟩
    intro i
    rw [Step0472.inputCoefficient,← Step0471.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0472.stepData=true ∧
      (∀ i : Fin 7, Step0473.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0472.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0472.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0472.allStagesChecked,?_,Step0472.initialMarginCheck⟩
    intro i
    rw [Step0473.inputCoefficient,← Step0472.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0473.stepData=true ∧
      (∀ i : Fin 7, Step0474.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0473.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0473.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0473.allStagesChecked,?_,Step0473.initialMarginCheck⟩
    intro i
    rw [Step0474.inputCoefficient,← Step0473.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0474.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0474.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0474.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0474.allStagesChecked,?_,Step0474.initialMarginCheck⟩
    intro i
    change Step0474.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0474.stepData)[i.val]
    rw [← Step0474.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0470.stepData.coefficient 0 i=Step0470.inputData[i.val]
  exact Step0470.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.Block0004
