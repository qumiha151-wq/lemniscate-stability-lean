import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0255
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0256
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0257
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0258
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0259

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0256.inputData=Step0255.endpointData := by decide +kernel

theorem glue1 : Step0257.inputData=Step0256.endpointData := by decide +kernel

theorem glue2 : Step0258.inputData=Step0257.endpointData := by decide +kernel

theorem glue3 : Step0259.inputData=Step0258.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0255.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0259.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0255.stepData
  | 1=>Step0256.stepData
  | 2=>Step0257.stepData
  | 3=>Step0258.stepData
  | 4=>Step0259.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0255.stepData=true ∧
      (∀ i : Fin 7, Step0256.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0255.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0255.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0255.allStagesChecked,?_,Step0255.initialMarginCheck⟩
    intro i
    rw [Step0256.inputCoefficient,← Step0255.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0256.stepData=true ∧
      (∀ i : Fin 7, Step0257.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0256.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0256.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0256.allStagesChecked,?_,Step0256.initialMarginCheck⟩
    intro i
    rw [Step0257.inputCoefficient,← Step0256.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0257.stepData=true ∧
      (∀ i : Fin 7, Step0258.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0257.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0257.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0257.allStagesChecked,?_,Step0257.initialMarginCheck⟩
    intro i
    rw [Step0258.inputCoefficient,← Step0257.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0258.stepData=true ∧
      (∀ i : Fin 7, Step0259.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0258.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0258.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0258.allStagesChecked,?_,Step0258.initialMarginCheck⟩
    intro i
    rw [Step0259.inputCoefficient,← Step0258.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0259.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0259.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0259.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0259.allStagesChecked,?_,Step0259.initialMarginCheck⟩
    intro i
    change Step0259.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0259.stepData)[i.val]
    rw [← Step0259.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0255.stepData.coefficient 0 i=Step0255.inputData[i.val]
  exact Step0255.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Block0001
