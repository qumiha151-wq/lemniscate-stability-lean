import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0640
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0641
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0642
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0643
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0644

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0641.inputData=Step0640.endpointData := by decide +kernel

theorem glue1 : Step0642.inputData=Step0641.endpointData := by decide +kernel

theorem glue2 : Step0643.inputData=Step0642.endpointData := by decide +kernel

theorem glue3 : Step0644.inputData=Step0643.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0640.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0644.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0640.stepData
  | 1=>Step0641.stepData
  | 2=>Step0642.stepData
  | 3=>Step0643.stepData
  | 4=>Step0644.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0640.stepData=true ∧
      (∀ i : Fin 7, Step0641.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0640.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0640.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0640.allStagesChecked,?_,Step0640.initialMarginCheck⟩
    intro i
    rw [Step0641.inputCoefficient,← Step0640.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0641.stepData=true ∧
      (∀ i : Fin 7, Step0642.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0641.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0641.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0641.allStagesChecked,?_,Step0641.initialMarginCheck⟩
    intro i
    rw [Step0642.inputCoefficient,← Step0641.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0642.stepData=true ∧
      (∀ i : Fin 7, Step0643.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0642.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0642.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0642.allStagesChecked,?_,Step0642.initialMarginCheck⟩
    intro i
    rw [Step0643.inputCoefficient,← Step0642.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0643.stepData=true ∧
      (∀ i : Fin 7, Step0644.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0643.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0643.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0643.allStagesChecked,?_,Step0643.initialMarginCheck⟩
    intro i
    rw [Step0644.inputCoefficient,← Step0643.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0644.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0644.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0644.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0644.allStagesChecked,?_,Step0644.initialMarginCheck⟩
    intro i
    change Step0644.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0644.stepData)[i.val]
    rw [← Step0644.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0640.stepData.coefficient 0 i=Step0640.inputData[i.val]
  exact Step0640.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Block0008
