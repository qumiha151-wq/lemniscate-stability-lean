import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0395
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0396
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0397
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0398
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0399

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0396.inputData=Step0395.endpointData := by decide +kernel

theorem glue1 : Step0397.inputData=Step0396.endpointData := by decide +kernel

theorem glue2 : Step0398.inputData=Step0397.endpointData := by decide +kernel

theorem glue3 : Step0399.inputData=Step0398.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0395.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0399.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0395.stepData
  | 1=>Step0396.stepData
  | 2=>Step0397.stepData
  | 3=>Step0398.stepData
  | 4=>Step0399.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0395.stepData=true ∧
      (∀ i : Fin 7, Step0396.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0395.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0395.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0395.allStagesChecked,?_,Step0395.initialMarginCheck⟩
    intro i
    rw [Step0396.inputCoefficient,← Step0395.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0396.stepData=true ∧
      (∀ i : Fin 7, Step0397.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0396.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0396.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0396.allStagesChecked,?_,Step0396.initialMarginCheck⟩
    intro i
    rw [Step0397.inputCoefficient,← Step0396.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0397.stepData=true ∧
      (∀ i : Fin 7, Step0398.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0397.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0397.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0397.allStagesChecked,?_,Step0397.initialMarginCheck⟩
    intro i
    rw [Step0398.inputCoefficient,← Step0397.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0398.stepData=true ∧
      (∀ i : Fin 7, Step0399.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0398.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0398.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0398.allStagesChecked,?_,Step0398.initialMarginCheck⟩
    intro i
    rw [Step0399.inputCoefficient,← Step0398.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0399.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0399.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0399.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0399.allStagesChecked,?_,Step0399.initialMarginCheck⟩
    intro i
    change Step0399.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0399.stepData)[i.val]
    rw [← Step0399.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0395.stepData.coefficient 0 i=Step0395.inputData[i.val]
  exact Step0395.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Block0009
