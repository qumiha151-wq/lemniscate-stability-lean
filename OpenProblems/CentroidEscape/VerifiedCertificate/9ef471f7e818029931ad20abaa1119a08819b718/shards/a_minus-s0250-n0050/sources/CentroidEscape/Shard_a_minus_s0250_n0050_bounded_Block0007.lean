import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0285
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0286
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0287
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0288
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0289

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0286.inputData=Step0285.endpointData := by decide +kernel

theorem glue1 : Step0287.inputData=Step0286.endpointData := by decide +kernel

theorem glue2 : Step0288.inputData=Step0287.endpointData := by decide +kernel

theorem glue3 : Step0289.inputData=Step0288.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0285.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0289.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0285.stepData
  | 1=>Step0286.stepData
  | 2=>Step0287.stepData
  | 3=>Step0288.stepData
  | 4=>Step0289.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0285.stepData=true ∧
      (∀ i : Fin 7, Step0286.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0285.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0285.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0285.allStagesChecked,?_,Step0285.initialMarginCheck⟩
    intro i
    rw [Step0286.inputCoefficient,← Step0285.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0286.stepData=true ∧
      (∀ i : Fin 7, Step0287.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0286.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0286.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0286.allStagesChecked,?_,Step0286.initialMarginCheck⟩
    intro i
    rw [Step0287.inputCoefficient,← Step0286.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0287.stepData=true ∧
      (∀ i : Fin 7, Step0288.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0287.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0287.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0287.allStagesChecked,?_,Step0287.initialMarginCheck⟩
    intro i
    rw [Step0288.inputCoefficient,← Step0287.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0288.stepData=true ∧
      (∀ i : Fin 7, Step0289.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0288.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0288.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0288.allStagesChecked,?_,Step0288.initialMarginCheck⟩
    intro i
    rw [Step0289.inputCoefficient,← Step0288.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0289.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0289.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0289.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0289.allStagesChecked,?_,Step0289.initialMarginCheck⟩
    intro i
    change Step0289.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0289.stepData)[i.val]
    rw [← Step0289.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0285.stepData.coefficient 0 i=Step0285.inputData[i.val]
  exact Step0285.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Block0007
