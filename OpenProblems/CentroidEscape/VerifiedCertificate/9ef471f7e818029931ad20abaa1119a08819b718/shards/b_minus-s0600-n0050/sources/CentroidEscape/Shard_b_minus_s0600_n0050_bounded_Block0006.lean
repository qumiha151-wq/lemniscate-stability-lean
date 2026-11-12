import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0600_n0050_bounded_Step0630
import CentroidEscape.Shard_b_minus_s0600_n0050_bounded_Step0631
import CentroidEscape.Shard_b_minus_s0600_n0050_bounded_Step0632
import CentroidEscape.Shard_b_minus_s0600_n0050_bounded_Step0633
import CentroidEscape.Shard_b_minus_s0600_n0050_bounded_Step0634

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0600_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0631.inputData=Step0630.endpointData := by decide +kernel

theorem glue1 : Step0632.inputData=Step0631.endpointData := by decide +kernel

theorem glue2 : Step0633.inputData=Step0632.endpointData := by decide +kernel

theorem glue3 : Step0634.inputData=Step0633.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0630.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0634.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0630.stepData
  | 1=>Step0631.stepData
  | 2=>Step0632.stepData
  | 3=>Step0633.stepData
  | 4=>Step0634.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0630.stepData=true ∧
      (∀ i : Fin 7, Step0631.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0630.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0630.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0630.allStagesChecked,?_,Step0630.initialMarginCheck⟩
    intro i
    rw [Step0631.inputCoefficient,← Step0630.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0631.stepData=true ∧
      (∀ i : Fin 7, Step0632.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0631.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0631.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0631.allStagesChecked,?_,Step0631.initialMarginCheck⟩
    intro i
    rw [Step0632.inputCoefficient,← Step0631.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0632.stepData=true ∧
      (∀ i : Fin 7, Step0633.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0632.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0632.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0632.allStagesChecked,?_,Step0632.initialMarginCheck⟩
    intro i
    rw [Step0633.inputCoefficient,← Step0632.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0633.stepData=true ∧
      (∀ i : Fin 7, Step0634.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0633.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0633.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0633.allStagesChecked,?_,Step0633.initialMarginCheck⟩
    intro i
    rw [Step0634.inputCoefficient,← Step0633.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0634.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0634.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0634.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0634.allStagesChecked,?_,Step0634.initialMarginCheck⟩
    intro i
    change Step0634.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0634.stepData)[i.val]
    rw [← Step0634.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0630.stepData.coefficient 0 i=Step0630.inputData[i.val]
  exact Step0630.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0600_n0050_bounded.Block0006
