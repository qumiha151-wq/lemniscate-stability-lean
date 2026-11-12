import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0250
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0251
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0252
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0253
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0254

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0251.inputData=Step0250.endpointData := by decide +kernel

theorem glue1 : Step0252.inputData=Step0251.endpointData := by decide +kernel

theorem glue2 : Step0253.inputData=Step0252.endpointData := by decide +kernel

theorem glue3 : Step0254.inputData=Step0253.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0250.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0254.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0250.stepData
  | 1=>Step0251.stepData
  | 2=>Step0252.stepData
  | 3=>Step0253.stepData
  | 4=>Step0254.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0250.stepData=true ∧
      (∀ i : Fin 7, Step0251.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0250.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0250.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0250.allStagesChecked,?_,Step0250.initialMarginCheck⟩
    intro i
    rw [Step0251.inputCoefficient,← Step0250.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0251.stepData=true ∧
      (∀ i : Fin 7, Step0252.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0251.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0251.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0251.allStagesChecked,?_,Step0251.initialMarginCheck⟩
    intro i
    rw [Step0252.inputCoefficient,← Step0251.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0252.stepData=true ∧
      (∀ i : Fin 7, Step0253.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0252.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0252.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0252.allStagesChecked,?_,Step0252.initialMarginCheck⟩
    intro i
    rw [Step0253.inputCoefficient,← Step0252.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0253.stepData=true ∧
      (∀ i : Fin 7, Step0254.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0253.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0253.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0253.allStagesChecked,?_,Step0253.initialMarginCheck⟩
    intro i
    rw [Step0254.inputCoefficient,← Step0253.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0254.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0254.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0254.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0254.allStagesChecked,?_,Step0254.initialMarginCheck⟩
    intro i
    change Step0254.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0254.stepData)[i.val]
    rw [← Step0254.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0250.stepData.coefficient 0 i=Step0250.inputData[i.val]
  exact Step0250.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Block0000
