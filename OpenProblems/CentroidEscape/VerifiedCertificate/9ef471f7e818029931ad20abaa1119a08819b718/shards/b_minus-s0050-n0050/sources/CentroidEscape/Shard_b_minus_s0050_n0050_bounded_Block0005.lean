import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Step0075
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Step0076
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Step0077
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Step0078
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Step0079

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0076.inputData=Step0075.endpointData := by decide +kernel

theorem glue1 : Step0077.inputData=Step0076.endpointData := by decide +kernel

theorem glue2 : Step0078.inputData=Step0077.endpointData := by decide +kernel

theorem glue3 : Step0079.inputData=Step0078.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0075.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0079.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0075.stepData
  | 1=>Step0076.stepData
  | 2=>Step0077.stepData
  | 3=>Step0078.stepData
  | 4=>Step0079.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0075.stepData=true ∧
      (∀ i : Fin 7, Step0076.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0075.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0075.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0075.allStagesChecked,?_,Step0075.initialMarginCheck⟩
    intro i
    rw [Step0076.inputCoefficient,← Step0075.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0076.stepData=true ∧
      (∀ i : Fin 7, Step0077.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0076.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0076.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0076.allStagesChecked,?_,Step0076.initialMarginCheck⟩
    intro i
    rw [Step0077.inputCoefficient,← Step0076.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0077.stepData=true ∧
      (∀ i : Fin 7, Step0078.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0077.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0077.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0077.allStagesChecked,?_,Step0077.initialMarginCheck⟩
    intro i
    rw [Step0078.inputCoefficient,← Step0077.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0078.stepData=true ∧
      (∀ i : Fin 7, Step0079.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0078.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0078.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0078.allStagesChecked,?_,Step0078.initialMarginCheck⟩
    intro i
    rw [Step0079.inputCoefficient,← Step0078.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0079.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0079.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0079.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0079.allStagesChecked,?_,Step0079.initialMarginCheck⟩
    intro i
    change Step0079.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0079.stepData)[i.val]
    rw [← Step0079.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0075.stepData.coefficient 0 i=Step0075.inputData[i.val]
  exact Step0075.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.Block0005
