import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0360
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0361
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0362
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0363
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0364

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0361.inputData=Step0360.endpointData := by decide +kernel

theorem glue1 : Step0362.inputData=Step0361.endpointData := by decide +kernel

theorem glue2 : Step0363.inputData=Step0362.endpointData := by decide +kernel

theorem glue3 : Step0364.inputData=Step0363.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0360.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0364.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0360.stepData
  | 1=>Step0361.stepData
  | 2=>Step0362.stepData
  | 3=>Step0363.stepData
  | 4=>Step0364.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0360.stepData=true ∧
      (∀ i : Fin 7, Step0361.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0360.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0360.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0360.allStagesChecked,?_,Step0360.initialMarginCheck⟩
    intro i
    rw [Step0361.inputCoefficient,← Step0360.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0361.stepData=true ∧
      (∀ i : Fin 7, Step0362.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0361.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0361.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0361.allStagesChecked,?_,Step0361.initialMarginCheck⟩
    intro i
    rw [Step0362.inputCoefficient,← Step0361.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0362.stepData=true ∧
      (∀ i : Fin 7, Step0363.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0362.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0362.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0362.allStagesChecked,?_,Step0362.initialMarginCheck⟩
    intro i
    rw [Step0363.inputCoefficient,← Step0362.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0363.stepData=true ∧
      (∀ i : Fin 7, Step0364.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0363.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0363.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0363.allStagesChecked,?_,Step0363.initialMarginCheck⟩
    intro i
    rw [Step0364.inputCoefficient,← Step0363.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0364.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0364.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0364.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0364.allStagesChecked,?_,Step0364.initialMarginCheck⟩
    intro i
    change Step0364.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0364.stepData)[i.val]
    rw [← Step0364.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0360.stepData.coefficient 0 i=Step0360.inputData[i.val]
  exact Step0360.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Block0002
