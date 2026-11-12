import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0650
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0651
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0652
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0653
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0654

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0651.inputData=Step0650.endpointData := by decide +kernel

theorem glue1 : Step0652.inputData=Step0651.endpointData := by decide +kernel

theorem glue2 : Step0653.inputData=Step0652.endpointData := by decide +kernel

theorem glue3 : Step0654.inputData=Step0653.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0650.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0654.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0650.stepData
  | 1=>Step0651.stepData
  | 2=>Step0652.stepData
  | 3=>Step0653.stepData
  | 4=>Step0654.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0650.stepData=true ∧
      (∀ i : Fin 7, Step0651.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0650.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0650.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0650.allStagesChecked,?_,Step0650.initialMarginCheck⟩
    intro i
    rw [Step0651.inputCoefficient,← Step0650.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0651.stepData=true ∧
      (∀ i : Fin 7, Step0652.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0651.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0651.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0651.allStagesChecked,?_,Step0651.initialMarginCheck⟩
    intro i
    rw [Step0652.inputCoefficient,← Step0651.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0652.stepData=true ∧
      (∀ i : Fin 7, Step0653.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0652.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0652.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0652.allStagesChecked,?_,Step0652.initialMarginCheck⟩
    intro i
    rw [Step0653.inputCoefficient,← Step0652.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0653.stepData=true ∧
      (∀ i : Fin 7, Step0654.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0653.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0653.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0653.allStagesChecked,?_,Step0653.initialMarginCheck⟩
    intro i
    rw [Step0654.inputCoefficient,← Step0653.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0654.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0654.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0654.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0654.allStagesChecked,?_,Step0654.initialMarginCheck⟩
    intro i
    change Step0654.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0654.stepData)[i.val]
    rw [← Step0654.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0650.stepData.coefficient 0 i=Step0650.inputData[i.val]
  exact Step0650.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Block0000
