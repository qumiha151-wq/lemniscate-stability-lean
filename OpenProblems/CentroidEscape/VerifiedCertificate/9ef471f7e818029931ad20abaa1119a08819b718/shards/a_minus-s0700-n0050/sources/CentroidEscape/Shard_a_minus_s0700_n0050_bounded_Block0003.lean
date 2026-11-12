import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0715
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0716
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0717
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0718
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0719

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0716.inputData=Step0715.endpointData := by decide +kernel

theorem glue1 : Step0717.inputData=Step0716.endpointData := by decide +kernel

theorem glue2 : Step0718.inputData=Step0717.endpointData := by decide +kernel

theorem glue3 : Step0719.inputData=Step0718.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0715.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0719.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0715.stepData
  | 1=>Step0716.stepData
  | 2=>Step0717.stepData
  | 3=>Step0718.stepData
  | 4=>Step0719.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0715.stepData=true ∧
      (∀ i : Fin 7, Step0716.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0715.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0715.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0715.allStagesChecked,?_,Step0715.initialMarginCheck⟩
    intro i
    rw [Step0716.inputCoefficient,← Step0715.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0716.stepData=true ∧
      (∀ i : Fin 7, Step0717.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0716.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0716.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0716.allStagesChecked,?_,Step0716.initialMarginCheck⟩
    intro i
    rw [Step0717.inputCoefficient,← Step0716.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0717.stepData=true ∧
      (∀ i : Fin 7, Step0718.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0717.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0717.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0717.allStagesChecked,?_,Step0717.initialMarginCheck⟩
    intro i
    rw [Step0718.inputCoefficient,← Step0717.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0718.stepData=true ∧
      (∀ i : Fin 7, Step0719.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0718.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0718.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0718.allStagesChecked,?_,Step0718.initialMarginCheck⟩
    intro i
    rw [Step0719.inputCoefficient,← Step0718.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0719.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0719.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0719.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0719.allStagesChecked,?_,Step0719.initialMarginCheck⟩
    intro i
    change Step0719.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0719.stepData)[i.val]
    rw [← Step0719.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0715.stepData.coefficient 0 i=Step0715.inputData[i.val]
  exact Step0715.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Block0003
