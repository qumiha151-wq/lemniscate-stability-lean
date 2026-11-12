import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Step0245
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Step0246
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Step0247
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Step0248
import CentroidEscape.Shard_a_minus_s0200_n0050_bounded_Step0249

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0246.inputData=Step0245.endpointData := by decide +kernel

theorem glue1 : Step0247.inputData=Step0246.endpointData := by decide +kernel

theorem glue2 : Step0248.inputData=Step0247.endpointData := by decide +kernel

theorem glue3 : Step0249.inputData=Step0248.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0245.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0249.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0245.stepData
  | 1=>Step0246.stepData
  | 2=>Step0247.stepData
  | 3=>Step0248.stepData
  | 4=>Step0249.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0245.stepData=true ∧
      (∀ i : Fin 7, Step0246.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0245.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0245.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0245.allStagesChecked,?_,Step0245.initialMarginCheck⟩
    intro i
    rw [Step0246.inputCoefficient,← Step0245.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0246.stepData=true ∧
      (∀ i : Fin 7, Step0247.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0246.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0246.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0246.allStagesChecked,?_,Step0246.initialMarginCheck⟩
    intro i
    rw [Step0247.inputCoefficient,← Step0246.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0247.stepData=true ∧
      (∀ i : Fin 7, Step0248.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0247.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0247.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0247.allStagesChecked,?_,Step0247.initialMarginCheck⟩
    intro i
    rw [Step0248.inputCoefficient,← Step0247.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0248.stepData=true ∧
      (∀ i : Fin 7, Step0249.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0248.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0248.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0248.allStagesChecked,?_,Step0248.initialMarginCheck⟩
    intro i
    rw [Step0249.inputCoefficient,← Step0248.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0249.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0249.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0249.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0249.allStagesChecked,?_,Step0249.initialMarginCheck⟩
    intro i
    change Step0249.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0249.stepData)[i.val]
    rw [← Step0249.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0245.stepData.coefficient 0 i=Step0245.inputData[i.val]
  exact Step0245.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0200_n0050_bounded.Block0009
