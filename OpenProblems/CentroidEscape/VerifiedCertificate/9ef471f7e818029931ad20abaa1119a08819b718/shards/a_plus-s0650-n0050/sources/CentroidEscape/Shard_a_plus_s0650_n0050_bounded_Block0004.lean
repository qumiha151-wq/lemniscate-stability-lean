import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0670
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0671
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0672
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0673
import CentroidEscape.Shard_a_plus_s0650_n0050_bounded_Step0674

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0671.inputData=Step0670.endpointData := by decide +kernel

theorem glue1 : Step0672.inputData=Step0671.endpointData := by decide +kernel

theorem glue2 : Step0673.inputData=Step0672.endpointData := by decide +kernel

theorem glue3 : Step0674.inputData=Step0673.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0670.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0674.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0670.stepData
  | 1=>Step0671.stepData
  | 2=>Step0672.stepData
  | 3=>Step0673.stepData
  | 4=>Step0674.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0670.stepData=true ∧
      (∀ i : Fin 7, Step0671.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0670.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0670.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0670.allStagesChecked,?_,Step0670.initialMarginCheck⟩
    intro i
    rw [Step0671.inputCoefficient,← Step0670.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0671.stepData=true ∧
      (∀ i : Fin 7, Step0672.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0671.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0671.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0671.allStagesChecked,?_,Step0671.initialMarginCheck⟩
    intro i
    rw [Step0672.inputCoefficient,← Step0671.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0672.stepData=true ∧
      (∀ i : Fin 7, Step0673.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0672.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0672.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0672.allStagesChecked,?_,Step0672.initialMarginCheck⟩
    intro i
    rw [Step0673.inputCoefficient,← Step0672.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0673.stepData=true ∧
      (∀ i : Fin 7, Step0674.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0673.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0673.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0673.allStagesChecked,?_,Step0673.initialMarginCheck⟩
    intro i
    rw [Step0674.inputCoefficient,← Step0673.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0674.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0674.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0674.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0674.allStagesChecked,?_,Step0674.initialMarginCheck⟩
    intro i
    change Step0674.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0674.stepData)[i.val]
    rw [← Step0674.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0670.stepData.coefficient 0 i=Step0670.inputData[i.val]
  exact Step0670.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0650_n0050_bounded.Block0004
