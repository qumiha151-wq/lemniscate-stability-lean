import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0100_n0050_bounded_Step0130
import CentroidEscape.Shard_center_s0100_n0050_bounded_Step0131
import CentroidEscape.Shard_center_s0100_n0050_bounded_Step0132
import CentroidEscape.Shard_center_s0100_n0050_bounded_Step0133
import CentroidEscape.Shard_center_s0100_n0050_bounded_Step0134

namespace CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0131.inputData=Step0130.endpointData := by decide +kernel

theorem glue1 : Step0132.inputData=Step0131.endpointData := by decide +kernel

theorem glue2 : Step0133.inputData=Step0132.endpointData := by decide +kernel

theorem glue3 : Step0134.inputData=Step0133.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0130.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0134.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0130.stepData
  | 1=>Step0131.stepData
  | 2=>Step0132.stepData
  | 3=>Step0133.stepData
  | 4=>Step0134.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0130.stepData=true ∧
      (∀ i : Fin 7, Step0131.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0130.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0130.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0130.allStagesChecked,?_,Step0130.initialMarginCheck⟩
    intro i
    rw [Step0131.inputCoefficient,← Step0130.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0131.stepData=true ∧
      (∀ i : Fin 7, Step0132.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0131.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0131.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0131.allStagesChecked,?_,Step0131.initialMarginCheck⟩
    intro i
    rw [Step0132.inputCoefficient,← Step0131.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0132.stepData=true ∧
      (∀ i : Fin 7, Step0133.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0132.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0132.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0132.allStagesChecked,?_,Step0132.initialMarginCheck⟩
    intro i
    rw [Step0133.inputCoefficient,← Step0132.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0133.stepData=true ∧
      (∀ i : Fin 7, Step0134.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0133.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0133.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0133.allStagesChecked,?_,Step0133.initialMarginCheck⟩
    intro i
    rw [Step0134.inputCoefficient,← Step0133.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0134.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0134.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0134.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0134.allStagesChecked,?_,Step0134.initialMarginCheck⟩
    intro i
    change Step0134.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0134.stepData)[i.val]
    rw [← Step0134.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0130.stepData.coefficient 0 i=Step0130.inputData[i.val]
  exact Step0130.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0100_n0050_bounded.Block0006
