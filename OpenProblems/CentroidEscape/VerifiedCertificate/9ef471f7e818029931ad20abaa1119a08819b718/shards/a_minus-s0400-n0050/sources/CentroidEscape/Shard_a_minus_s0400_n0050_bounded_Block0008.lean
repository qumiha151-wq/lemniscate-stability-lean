import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0400_n0050_bounded_Step0440
import CentroidEscape.Shard_a_minus_s0400_n0050_bounded_Step0441
import CentroidEscape.Shard_a_minus_s0400_n0050_bounded_Step0442
import CentroidEscape.Shard_a_minus_s0400_n0050_bounded_Step0443
import CentroidEscape.Shard_a_minus_s0400_n0050_bounded_Step0444

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0400_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0441.inputData=Step0440.endpointData := by decide +kernel

theorem glue1 : Step0442.inputData=Step0441.endpointData := by decide +kernel

theorem glue2 : Step0443.inputData=Step0442.endpointData := by decide +kernel

theorem glue3 : Step0444.inputData=Step0443.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0440.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0444.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0440.stepData
  | 1=>Step0441.stepData
  | 2=>Step0442.stepData
  | 3=>Step0443.stepData
  | 4=>Step0444.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0440.stepData=true ∧
      (∀ i : Fin 7, Step0441.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0440.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0440.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0440.allStagesChecked,?_,Step0440.initialMarginCheck⟩
    intro i
    rw [Step0441.inputCoefficient,← Step0440.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0441.stepData=true ∧
      (∀ i : Fin 7, Step0442.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0441.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0441.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0441.allStagesChecked,?_,Step0441.initialMarginCheck⟩
    intro i
    rw [Step0442.inputCoefficient,← Step0441.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0442.stepData=true ∧
      (∀ i : Fin 7, Step0443.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0442.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0442.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0442.allStagesChecked,?_,Step0442.initialMarginCheck⟩
    intro i
    rw [Step0443.inputCoefficient,← Step0442.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0443.stepData=true ∧
      (∀ i : Fin 7, Step0444.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0443.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0443.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0443.allStagesChecked,?_,Step0443.initialMarginCheck⟩
    intro i
    rw [Step0444.inputCoefficient,← Step0443.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0444.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0444.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0444.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0444.allStagesChecked,?_,Step0444.initialMarginCheck⟩
    intro i
    change Step0444.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0444.stepData)[i.val]
    rw [← Step0444.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0440.stepData.coefficient 0 i=Step0440.inputData[i.val]
  exact Step0440.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0400_n0050_bounded.Block0008
