import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0390
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0391
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0392
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0393
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0394

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0391.inputData=Step0390.endpointData := by decide +kernel

theorem glue1 : Step0392.inputData=Step0391.endpointData := by decide +kernel

theorem glue2 : Step0393.inputData=Step0392.endpointData := by decide +kernel

theorem glue3 : Step0394.inputData=Step0393.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0390.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0394.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0390.stepData
  | 1=>Step0391.stepData
  | 2=>Step0392.stepData
  | 3=>Step0393.stepData
  | 4=>Step0394.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0390.stepData=true ∧
      (∀ i : Fin 7, Step0391.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0390.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0390.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0390.allStagesChecked,?_,Step0390.initialMarginCheck⟩
    intro i
    rw [Step0391.inputCoefficient,← Step0390.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0391.stepData=true ∧
      (∀ i : Fin 7, Step0392.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0391.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0391.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0391.allStagesChecked,?_,Step0391.initialMarginCheck⟩
    intro i
    rw [Step0392.inputCoefficient,← Step0391.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0392.stepData=true ∧
      (∀ i : Fin 7, Step0393.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0392.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0392.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0392.allStagesChecked,?_,Step0392.initialMarginCheck⟩
    intro i
    rw [Step0393.inputCoefficient,← Step0392.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0393.stepData=true ∧
      (∀ i : Fin 7, Step0394.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0393.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0393.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0393.allStagesChecked,?_,Step0393.initialMarginCheck⟩
    intro i
    rw [Step0394.inputCoefficient,← Step0393.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0394.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0394.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0394.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0394.allStagesChecked,?_,Step0394.initialMarginCheck⟩
    intro i
    change Step0394.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0394.stepData)[i.val]
    rw [← Step0394.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0390.stepData.coefficient 0 i=Step0390.inputData[i.val]
  exact Step0390.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Block0008
