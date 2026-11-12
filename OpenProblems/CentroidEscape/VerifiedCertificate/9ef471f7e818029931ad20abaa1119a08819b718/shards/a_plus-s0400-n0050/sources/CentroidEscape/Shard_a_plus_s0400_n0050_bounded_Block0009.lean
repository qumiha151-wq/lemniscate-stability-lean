import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Step0445
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Step0446
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Step0447
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Step0448
import CentroidEscape.Shard_a_plus_s0400_n0050_bounded_Step0449

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0446.inputData=Step0445.endpointData := by decide +kernel

theorem glue1 : Step0447.inputData=Step0446.endpointData := by decide +kernel

theorem glue2 : Step0448.inputData=Step0447.endpointData := by decide +kernel

theorem glue3 : Step0449.inputData=Step0448.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0445.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0449.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0445.stepData
  | 1=>Step0446.stepData
  | 2=>Step0447.stepData
  | 3=>Step0448.stepData
  | 4=>Step0449.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0445.stepData=true ∧
      (∀ i : Fin 7, Step0446.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0445.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0445.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0445.allStagesChecked,?_,Step0445.initialMarginCheck⟩
    intro i
    rw [Step0446.inputCoefficient,← Step0445.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0446.stepData=true ∧
      (∀ i : Fin 7, Step0447.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0446.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0446.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0446.allStagesChecked,?_,Step0446.initialMarginCheck⟩
    intro i
    rw [Step0447.inputCoefficient,← Step0446.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0447.stepData=true ∧
      (∀ i : Fin 7, Step0448.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0447.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0447.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0447.allStagesChecked,?_,Step0447.initialMarginCheck⟩
    intro i
    rw [Step0448.inputCoefficient,← Step0447.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0448.stepData=true ∧
      (∀ i : Fin 7, Step0449.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0448.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0448.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0448.allStagesChecked,?_,Step0448.initialMarginCheck⟩
    intro i
    rw [Step0449.inputCoefficient,← Step0448.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0449.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0449.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0449.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0449.allStagesChecked,?_,Step0449.initialMarginCheck⟩
    intro i
    change Step0449.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0449.stepData)[i.val]
    rw [← Step0449.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0445.stepData.coefficient 0 i=Step0445.inputData[i.val]
  exact Step0445.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0400_n0050_bounded.Block0009
