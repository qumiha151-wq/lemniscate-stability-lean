import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0500_n0050_bounded_Step0500
import CentroidEscape.Shard_b_minus_s0500_n0050_bounded_Step0501
import CentroidEscape.Shard_b_minus_s0500_n0050_bounded_Step0502
import CentroidEscape.Shard_b_minus_s0500_n0050_bounded_Step0503
import CentroidEscape.Shard_b_minus_s0500_n0050_bounded_Step0504

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0500_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0501.inputData=Step0500.endpointData := by decide +kernel

theorem glue1 : Step0502.inputData=Step0501.endpointData := by decide +kernel

theorem glue2 : Step0503.inputData=Step0502.endpointData := by decide +kernel

theorem glue3 : Step0504.inputData=Step0503.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0500.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0504.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0500.stepData
  | 1=>Step0501.stepData
  | 2=>Step0502.stepData
  | 3=>Step0503.stepData
  | 4=>Step0504.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0500.stepData=true ∧
      (∀ i : Fin 7, Step0501.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0500.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0500.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0500.allStagesChecked,?_,Step0500.initialMarginCheck⟩
    intro i
    rw [Step0501.inputCoefficient,← Step0500.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0501.stepData=true ∧
      (∀ i : Fin 7, Step0502.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0501.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0501.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0501.allStagesChecked,?_,Step0501.initialMarginCheck⟩
    intro i
    rw [Step0502.inputCoefficient,← Step0501.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0502.stepData=true ∧
      (∀ i : Fin 7, Step0503.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0502.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0502.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0502.allStagesChecked,?_,Step0502.initialMarginCheck⟩
    intro i
    rw [Step0503.inputCoefficient,← Step0502.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0503.stepData=true ∧
      (∀ i : Fin 7, Step0504.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0503.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0503.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0503.allStagesChecked,?_,Step0503.initialMarginCheck⟩
    intro i
    rw [Step0504.inputCoefficient,← Step0503.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0504.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0504.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0504.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0504.allStagesChecked,?_,Step0504.initialMarginCheck⟩
    intro i
    change Step0504.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0504.stepData)[i.val]
    rw [← Step0504.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0500.stepData.coefficient 0 i=Step0500.inputData[i.val]
  exact Step0500.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0500_n0050_bounded.Block0000
