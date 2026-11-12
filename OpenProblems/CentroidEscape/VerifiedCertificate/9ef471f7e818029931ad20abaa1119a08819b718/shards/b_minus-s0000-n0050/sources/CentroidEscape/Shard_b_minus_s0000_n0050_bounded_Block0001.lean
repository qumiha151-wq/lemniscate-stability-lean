import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Step0005
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Step0006
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Step0007
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Step0008
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Step0009

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0000_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0006.inputData=Step0005.endpointData := by decide +kernel

theorem glue1 : Step0007.inputData=Step0006.endpointData := by decide +kernel

theorem glue2 : Step0008.inputData=Step0007.endpointData := by decide +kernel

theorem glue3 : Step0009.inputData=Step0008.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0005.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0009.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0005.stepData
  | 1=>Step0006.stepData
  | 2=>Step0007.stepData
  | 3=>Step0008.stepData
  | 4=>Step0009.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0005.stepData=true ∧
      (∀ i : Fin 7, Step0006.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0005.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0005.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0005.allStagesChecked,?_,Step0005.initialMarginCheck⟩
    intro i
    rw [Step0006.inputCoefficient,← Step0005.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0006.stepData=true ∧
      (∀ i : Fin 7, Step0007.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0006.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0006.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0006.allStagesChecked,?_,Step0006.initialMarginCheck⟩
    intro i
    rw [Step0007.inputCoefficient,← Step0006.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0007.stepData=true ∧
      (∀ i : Fin 7, Step0008.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0007.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0007.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0007.allStagesChecked,?_,Step0007.initialMarginCheck⟩
    intro i
    rw [Step0008.inputCoefficient,← Step0007.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0008.stepData=true ∧
      (∀ i : Fin 7, Step0009.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0008.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0008.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0008.allStagesChecked,?_,Step0008.initialMarginCheck⟩
    intro i
    rw [Step0009.inputCoefficient,← Step0008.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0009.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0009.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0009.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0009.allStagesChecked,?_,Step0009.initialMarginCheck⟩
    intro i
    change Step0009.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0009.stepData)[i.val]
    rw [← Step0009.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0005.stepData.coefficient 0 i=Step0005.inputData[i.val]
  exact Step0005.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0000_n0050_bounded.Block0001
