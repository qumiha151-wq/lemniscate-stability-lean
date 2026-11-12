import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Step0435
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Step0436
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Step0437
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Step0438
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Step0439

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0436.inputData=Step0435.endpointData := by decide +kernel

theorem glue1 : Step0437.inputData=Step0436.endpointData := by decide +kernel

theorem glue2 : Step0438.inputData=Step0437.endpointData := by decide +kernel

theorem glue3 : Step0439.inputData=Step0438.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0435.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0439.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0435.stepData
  | 1=>Step0436.stepData
  | 2=>Step0437.stepData
  | 3=>Step0438.stepData
  | 4=>Step0439.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0435.stepData=true ∧
      (∀ i : Fin 7, Step0436.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0435.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0435.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0435.allStagesChecked,?_,Step0435.initialMarginCheck⟩
    intro i
    rw [Step0436.inputCoefficient,← Step0435.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0436.stepData=true ∧
      (∀ i : Fin 7, Step0437.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0436.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0436.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0436.allStagesChecked,?_,Step0436.initialMarginCheck⟩
    intro i
    rw [Step0437.inputCoefficient,← Step0436.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0437.stepData=true ∧
      (∀ i : Fin 7, Step0438.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0437.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0437.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0437.allStagesChecked,?_,Step0437.initialMarginCheck⟩
    intro i
    rw [Step0438.inputCoefficient,← Step0437.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0438.stepData=true ∧
      (∀ i : Fin 7, Step0439.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0438.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0438.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0438.allStagesChecked,?_,Step0438.initialMarginCheck⟩
    intro i
    rw [Step0439.inputCoefficient,← Step0438.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0439.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0439.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0439.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0439.allStagesChecked,?_,Step0439.initialMarginCheck⟩
    intro i
    change Step0439.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0439.stepData)[i.val]
    rw [← Step0439.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0435.stepData.coefficient 0 i=Step0435.inputData[i.val]
  exact Step0435.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.Block0007
