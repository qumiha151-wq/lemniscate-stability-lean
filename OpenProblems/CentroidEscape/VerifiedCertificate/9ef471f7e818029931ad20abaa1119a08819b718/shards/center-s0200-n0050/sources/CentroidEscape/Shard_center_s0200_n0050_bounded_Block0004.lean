import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0220
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0221
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0222
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0223
import CentroidEscape.Shard_center_s0200_n0050_bounded_Step0224

namespace CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0221.inputData=Step0220.endpointData := by decide +kernel

theorem glue1 : Step0222.inputData=Step0221.endpointData := by decide +kernel

theorem glue2 : Step0223.inputData=Step0222.endpointData := by decide +kernel

theorem glue3 : Step0224.inputData=Step0223.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0220.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0224.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0220.stepData
  | 1=>Step0221.stepData
  | 2=>Step0222.stepData
  | 3=>Step0223.stepData
  | 4=>Step0224.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0220.stepData=true ∧
      (∀ i : Fin 7, Step0221.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0220.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0220.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0220.allStagesChecked,?_,Step0220.initialMarginCheck⟩
    intro i
    rw [Step0221.inputCoefficient,← Step0220.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0221.stepData=true ∧
      (∀ i : Fin 7, Step0222.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0221.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0221.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0221.allStagesChecked,?_,Step0221.initialMarginCheck⟩
    intro i
    rw [Step0222.inputCoefficient,← Step0221.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0222.stepData=true ∧
      (∀ i : Fin 7, Step0223.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0222.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0222.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0222.allStagesChecked,?_,Step0222.initialMarginCheck⟩
    intro i
    rw [Step0223.inputCoefficient,← Step0222.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0223.stepData=true ∧
      (∀ i : Fin 7, Step0224.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0223.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0223.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0223.allStagesChecked,?_,Step0223.initialMarginCheck⟩
    intro i
    rw [Step0224.inputCoefficient,← Step0223.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0224.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0224.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0224.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0224.allStagesChecked,?_,Step0224.initialMarginCheck⟩
    intro i
    change Step0224.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0224.stepData)[i.val]
    rw [← Step0224.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0220.stepData.coefficient 0 i=Step0220.inputData[i.val]
  exact Step0220.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0200_n0050_bounded.Block0004
