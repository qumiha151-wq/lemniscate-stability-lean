import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0150
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0151
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0152
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0153
import CentroidEscape.Shard_center_s0150_n0050_bounded_Step0154

namespace CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0151.inputData=Step0150.endpointData := by decide +kernel

theorem glue1 : Step0152.inputData=Step0151.endpointData := by decide +kernel

theorem glue2 : Step0153.inputData=Step0152.endpointData := by decide +kernel

theorem glue3 : Step0154.inputData=Step0153.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0150.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0154.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0150.stepData
  | 1=>Step0151.stepData
  | 2=>Step0152.stepData
  | 3=>Step0153.stepData
  | 4=>Step0154.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0150.stepData=true ∧
      (∀ i : Fin 7, Step0151.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0150.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0150.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0150.allStagesChecked,?_,Step0150.initialMarginCheck⟩
    intro i
    rw [Step0151.inputCoefficient,← Step0150.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0151.stepData=true ∧
      (∀ i : Fin 7, Step0152.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0151.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0151.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0151.allStagesChecked,?_,Step0151.initialMarginCheck⟩
    intro i
    rw [Step0152.inputCoefficient,← Step0151.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0152.stepData=true ∧
      (∀ i : Fin 7, Step0153.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0152.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0152.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0152.allStagesChecked,?_,Step0152.initialMarginCheck⟩
    intro i
    rw [Step0153.inputCoefficient,← Step0152.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0153.stepData=true ∧
      (∀ i : Fin 7, Step0154.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0153.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0153.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0153.allStagesChecked,?_,Step0153.initialMarginCheck⟩
    intro i
    rw [Step0154.inputCoefficient,← Step0153.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0154.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0154.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0154.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0154.allStagesChecked,?_,Step0154.initialMarginCheck⟩
    intro i
    change Step0154.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0154.stepData)[i.val]
    rw [← Step0154.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0150.stepData.coefficient 0 i=Step0150.inputData[i.val]
  exact Step0150.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0150_n0050_bounded.Block0000
