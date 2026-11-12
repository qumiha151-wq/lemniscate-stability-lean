import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0350
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0351
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0352
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0353
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0354

namespace CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0351.inputData=Step0350.endpointData := by decide +kernel

theorem glue1 : Step0352.inputData=Step0351.endpointData := by decide +kernel

theorem glue2 : Step0353.inputData=Step0352.endpointData := by decide +kernel

theorem glue3 : Step0354.inputData=Step0353.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0350.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0354.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0350.stepData
  | 1=>Step0351.stepData
  | 2=>Step0352.stepData
  | 3=>Step0353.stepData
  | 4=>Step0354.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0350.stepData=true ∧
      (∀ i : Fin 7, Step0351.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0350.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0350.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0350.allStagesChecked,?_,Step0350.initialMarginCheck⟩
    intro i
    rw [Step0351.inputCoefficient,← Step0350.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0351.stepData=true ∧
      (∀ i : Fin 7, Step0352.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0351.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0351.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0351.allStagesChecked,?_,Step0351.initialMarginCheck⟩
    intro i
    rw [Step0352.inputCoefficient,← Step0351.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0352.stepData=true ∧
      (∀ i : Fin 7, Step0353.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0352.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0352.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0352.allStagesChecked,?_,Step0352.initialMarginCheck⟩
    intro i
    rw [Step0353.inputCoefficient,← Step0352.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0353.stepData=true ∧
      (∀ i : Fin 7, Step0354.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0353.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0353.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0353.allStagesChecked,?_,Step0353.initialMarginCheck⟩
    intro i
    rw [Step0354.inputCoefficient,← Step0353.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0354.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0354.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0354.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0354.allStagesChecked,?_,Step0354.initialMarginCheck⟩
    intro i
    change Step0354.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0354.stepData)[i.val]
    rw [← Step0354.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0350.stepData.coefficient 0 i=Step0350.inputData[i.val]
  exact Step0350.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Block0000
