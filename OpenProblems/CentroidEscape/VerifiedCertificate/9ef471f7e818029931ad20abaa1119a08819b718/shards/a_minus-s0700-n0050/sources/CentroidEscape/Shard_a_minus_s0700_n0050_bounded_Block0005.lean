import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0725
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0726
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0727
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0728
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0729

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0726.inputData=Step0725.endpointData := by decide +kernel

theorem glue1 : Step0727.inputData=Step0726.endpointData := by decide +kernel

theorem glue2 : Step0728.inputData=Step0727.endpointData := by decide +kernel

theorem glue3 : Step0729.inputData=Step0728.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0725.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0729.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0725.stepData
  | 1=>Step0726.stepData
  | 2=>Step0727.stepData
  | 3=>Step0728.stepData
  | 4=>Step0729.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0725.stepData=true ∧
      (∀ i : Fin 7, Step0726.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0725.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0725.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0725.allStagesChecked,?_,Step0725.initialMarginCheck⟩
    intro i
    rw [Step0726.inputCoefficient,← Step0725.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0726.stepData=true ∧
      (∀ i : Fin 7, Step0727.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0726.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0726.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0726.allStagesChecked,?_,Step0726.initialMarginCheck⟩
    intro i
    rw [Step0727.inputCoefficient,← Step0726.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0727.stepData=true ∧
      (∀ i : Fin 7, Step0728.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0727.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0727.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0727.allStagesChecked,?_,Step0727.initialMarginCheck⟩
    intro i
    rw [Step0728.inputCoefficient,← Step0727.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0728.stepData=true ∧
      (∀ i : Fin 7, Step0729.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0728.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0728.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0728.allStagesChecked,?_,Step0728.initialMarginCheck⟩
    intro i
    rw [Step0729.inputCoefficient,← Step0728.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0729.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0729.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0729.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0729.allStagesChecked,?_,Step0729.initialMarginCheck⟩
    intro i
    change Step0729.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0729.stepData)[i.val]
    rw [← Step0729.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0725.stepData.coefficient 0 i=Step0725.inputData[i.val]
  exact Step0725.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Block0005
