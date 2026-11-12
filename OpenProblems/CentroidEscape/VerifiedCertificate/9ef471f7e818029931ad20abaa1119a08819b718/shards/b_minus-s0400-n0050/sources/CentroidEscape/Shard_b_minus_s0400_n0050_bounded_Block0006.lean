import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0430
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0431
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0432
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0433
import CentroidEscape.Shard_b_minus_s0400_n0050_bounded_Step0434

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0431.inputData=Step0430.endpointData := by decide +kernel

theorem glue1 : Step0432.inputData=Step0431.endpointData := by decide +kernel

theorem glue2 : Step0433.inputData=Step0432.endpointData := by decide +kernel

theorem glue3 : Step0434.inputData=Step0433.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0430.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0434.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0430.stepData
  | 1=>Step0431.stepData
  | 2=>Step0432.stepData
  | 3=>Step0433.stepData
  | 4=>Step0434.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0430.stepData=true ∧
      (∀ i : Fin 7, Step0431.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0430.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0430.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0430.allStagesChecked,?_,Step0430.initialMarginCheck⟩
    intro i
    rw [Step0431.inputCoefficient,← Step0430.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0431.stepData=true ∧
      (∀ i : Fin 7, Step0432.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0431.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0431.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0431.allStagesChecked,?_,Step0431.initialMarginCheck⟩
    intro i
    rw [Step0432.inputCoefficient,← Step0431.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0432.stepData=true ∧
      (∀ i : Fin 7, Step0433.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0432.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0432.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0432.allStagesChecked,?_,Step0432.initialMarginCheck⟩
    intro i
    rw [Step0433.inputCoefficient,← Step0432.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0433.stepData=true ∧
      (∀ i : Fin 7, Step0434.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0433.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0433.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0433.allStagesChecked,?_,Step0433.initialMarginCheck⟩
    intro i
    rw [Step0434.inputCoefficient,← Step0433.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0434.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0434.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0434.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0434.allStagesChecked,?_,Step0434.initialMarginCheck⟩
    intro i
    change Step0434.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0434.stepData)[i.val]
    rw [← Step0434.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0430.stepData.coefficient 0 i=Step0430.inputData[i.val]
  exact Step0430.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0400_n0050_bounded.Block0006
