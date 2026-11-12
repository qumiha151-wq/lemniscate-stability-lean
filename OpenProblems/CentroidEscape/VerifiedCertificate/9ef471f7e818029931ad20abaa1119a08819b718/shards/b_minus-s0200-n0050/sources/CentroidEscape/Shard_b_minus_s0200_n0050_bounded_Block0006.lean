import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0230
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0231
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0232
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0233
import CentroidEscape.Shard_b_minus_s0200_n0050_bounded_Step0234

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0231.inputData=Step0230.endpointData := by decide +kernel

theorem glue1 : Step0232.inputData=Step0231.endpointData := by decide +kernel

theorem glue2 : Step0233.inputData=Step0232.endpointData := by decide +kernel

theorem glue3 : Step0234.inputData=Step0233.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0230.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0234.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0230.stepData
  | 1=>Step0231.stepData
  | 2=>Step0232.stepData
  | 3=>Step0233.stepData
  | 4=>Step0234.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0230.stepData=true ∧
      (∀ i : Fin 7, Step0231.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0230.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0230.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0230.allStagesChecked,?_,Step0230.initialMarginCheck⟩
    intro i
    rw [Step0231.inputCoefficient,← Step0230.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0231.stepData=true ∧
      (∀ i : Fin 7, Step0232.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0231.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0231.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0231.allStagesChecked,?_,Step0231.initialMarginCheck⟩
    intro i
    rw [Step0232.inputCoefficient,← Step0231.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0232.stepData=true ∧
      (∀ i : Fin 7, Step0233.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0232.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0232.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0232.allStagesChecked,?_,Step0232.initialMarginCheck⟩
    intro i
    rw [Step0233.inputCoefficient,← Step0232.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0233.stepData=true ∧
      (∀ i : Fin 7, Step0234.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0233.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0233.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0233.allStagesChecked,?_,Step0233.initialMarginCheck⟩
    intro i
    rw [Step0234.inputCoefficient,← Step0233.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0234.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0234.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0234.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0234.allStagesChecked,?_,Step0234.initialMarginCheck⟩
    intro i
    change Step0234.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0234.stepData)[i.val]
    rw [← Step0234.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0230.stepData.coefficient 0 i=Step0230.inputData[i.val]
  exact Step0230.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0200_n0050_bounded.Block0006
