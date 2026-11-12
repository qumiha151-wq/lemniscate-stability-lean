import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0380
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0381
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0382
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0383
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0384

namespace CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0381.inputData=Step0380.endpointData := by decide +kernel

theorem glue1 : Step0382.inputData=Step0381.endpointData := by decide +kernel

theorem glue2 : Step0383.inputData=Step0382.endpointData := by decide +kernel

theorem glue3 : Step0384.inputData=Step0383.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0380.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0384.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0380.stepData
  | 1=>Step0381.stepData
  | 2=>Step0382.stepData
  | 3=>Step0383.stepData
  | 4=>Step0384.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0380.stepData=true ∧
      (∀ i : Fin 7, Step0381.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0380.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0380.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0380.allStagesChecked,?_,Step0380.initialMarginCheck⟩
    intro i
    rw [Step0381.inputCoefficient,← Step0380.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0381.stepData=true ∧
      (∀ i : Fin 7, Step0382.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0381.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0381.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0381.allStagesChecked,?_,Step0381.initialMarginCheck⟩
    intro i
    rw [Step0382.inputCoefficient,← Step0381.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0382.stepData=true ∧
      (∀ i : Fin 7, Step0383.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0382.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0382.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0382.allStagesChecked,?_,Step0382.initialMarginCheck⟩
    intro i
    rw [Step0383.inputCoefficient,← Step0382.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0383.stepData=true ∧
      (∀ i : Fin 7, Step0384.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0383.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0383.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0383.allStagesChecked,?_,Step0383.initialMarginCheck⟩
    intro i
    rw [Step0384.inputCoefficient,← Step0383.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0384.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0384.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0384.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0384.allStagesChecked,?_,Step0384.initialMarginCheck⟩
    intro i
    change Step0384.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0384.stepData)[i.val]
    rw [← Step0384.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0380.stepData.coefficient 0 i=Step0380.inputData[i.val]
  exact Step0380.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Block0006
