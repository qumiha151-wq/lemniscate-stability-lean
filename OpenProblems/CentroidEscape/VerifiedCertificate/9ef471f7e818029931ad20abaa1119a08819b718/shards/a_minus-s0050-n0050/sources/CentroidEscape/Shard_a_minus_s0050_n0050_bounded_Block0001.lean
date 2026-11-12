import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Step0055
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Step0056
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Step0057
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Step0058
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Step0059

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0056.inputData=Step0055.endpointData := by decide +kernel

theorem glue1 : Step0057.inputData=Step0056.endpointData := by decide +kernel

theorem glue2 : Step0058.inputData=Step0057.endpointData := by decide +kernel

theorem glue3 : Step0059.inputData=Step0058.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0055.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0059.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0055.stepData
  | 1=>Step0056.stepData
  | 2=>Step0057.stepData
  | 3=>Step0058.stepData
  | 4=>Step0059.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0055.stepData=true ∧
      (∀ i : Fin 7, Step0056.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0055.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0055.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0055.allStagesChecked,?_,Step0055.initialMarginCheck⟩
    intro i
    rw [Step0056.inputCoefficient,← Step0055.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0056.stepData=true ∧
      (∀ i : Fin 7, Step0057.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0056.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0056.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0056.allStagesChecked,?_,Step0056.initialMarginCheck⟩
    intro i
    rw [Step0057.inputCoefficient,← Step0056.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0057.stepData=true ∧
      (∀ i : Fin 7, Step0058.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0057.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0057.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0057.allStagesChecked,?_,Step0057.initialMarginCheck⟩
    intro i
    rw [Step0058.inputCoefficient,← Step0057.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0058.stepData=true ∧
      (∀ i : Fin 7, Step0059.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0058.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0058.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0058.allStagesChecked,?_,Step0058.initialMarginCheck⟩
    intro i
    rw [Step0059.inputCoefficient,← Step0058.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0059.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0059.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0059.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0059.allStagesChecked,?_,Step0059.initialMarginCheck⟩
    intro i
    change Step0059.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0059.stepData)[i.val]
    rw [← Step0059.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0055.stepData.coefficient 0 i=Step0055.inputData[i.val]
  exact Step0055.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.Block0001
