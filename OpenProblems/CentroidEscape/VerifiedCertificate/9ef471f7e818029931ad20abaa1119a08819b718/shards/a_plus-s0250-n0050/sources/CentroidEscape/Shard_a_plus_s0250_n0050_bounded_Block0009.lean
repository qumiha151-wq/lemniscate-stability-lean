import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0250_n0050_bounded_Step0295
import CentroidEscape.Shard_a_plus_s0250_n0050_bounded_Step0296
import CentroidEscape.Shard_a_plus_s0250_n0050_bounded_Step0297
import CentroidEscape.Shard_a_plus_s0250_n0050_bounded_Step0298
import CentroidEscape.Shard_a_plus_s0250_n0050_bounded_Step0299

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0250_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0296.inputData=Step0295.endpointData := by decide +kernel

theorem glue1 : Step0297.inputData=Step0296.endpointData := by decide +kernel

theorem glue2 : Step0298.inputData=Step0297.endpointData := by decide +kernel

theorem glue3 : Step0299.inputData=Step0298.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0295.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0299.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0295.stepData
  | 1=>Step0296.stepData
  | 2=>Step0297.stepData
  | 3=>Step0298.stepData
  | 4=>Step0299.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0295.stepData=true ∧
      (∀ i : Fin 7, Step0296.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0295.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0295.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0295.allStagesChecked,?_,Step0295.initialMarginCheck⟩
    intro i
    rw [Step0296.inputCoefficient,← Step0295.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0296.stepData=true ∧
      (∀ i : Fin 7, Step0297.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0296.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0296.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0296.allStagesChecked,?_,Step0296.initialMarginCheck⟩
    intro i
    rw [Step0297.inputCoefficient,← Step0296.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0297.stepData=true ∧
      (∀ i : Fin 7, Step0298.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0297.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0297.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0297.allStagesChecked,?_,Step0297.initialMarginCheck⟩
    intro i
    rw [Step0298.inputCoefficient,← Step0297.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0298.stepData=true ∧
      (∀ i : Fin 7, Step0299.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0298.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0298.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0298.allStagesChecked,?_,Step0298.initialMarginCheck⟩
    intro i
    rw [Step0299.inputCoefficient,← Step0298.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0299.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0299.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0299.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0299.allStagesChecked,?_,Step0299.initialMarginCheck⟩
    intro i
    change Step0299.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0299.stepData)[i.val]
    rw [← Step0299.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0295.stepData.coefficient 0 i=Step0295.inputData[i.val]
  exact Step0295.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0250_n0050_bounded.Block0009
