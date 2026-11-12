import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Step0315
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Step0316
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Step0317
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Step0318
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Step0319

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0316.inputData=Step0315.endpointData := by decide +kernel

theorem glue1 : Step0317.inputData=Step0316.endpointData := by decide +kernel

theorem glue2 : Step0318.inputData=Step0317.endpointData := by decide +kernel

theorem glue3 : Step0319.inputData=Step0318.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0315.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0319.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0315.stepData
  | 1=>Step0316.stepData
  | 2=>Step0317.stepData
  | 3=>Step0318.stepData
  | 4=>Step0319.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0315.stepData=true ∧
      (∀ i : Fin 7, Step0316.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0315.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0315.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0315.allStagesChecked,?_,Step0315.initialMarginCheck⟩
    intro i
    rw [Step0316.inputCoefficient,← Step0315.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0316.stepData=true ∧
      (∀ i : Fin 7, Step0317.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0316.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0316.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0316.allStagesChecked,?_,Step0316.initialMarginCheck⟩
    intro i
    rw [Step0317.inputCoefficient,← Step0316.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0317.stepData=true ∧
      (∀ i : Fin 7, Step0318.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0317.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0317.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0317.allStagesChecked,?_,Step0317.initialMarginCheck⟩
    intro i
    rw [Step0318.inputCoefficient,← Step0317.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0318.stepData=true ∧
      (∀ i : Fin 7, Step0319.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0318.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0318.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0318.allStagesChecked,?_,Step0318.initialMarginCheck⟩
    intro i
    rw [Step0319.inputCoefficient,← Step0318.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0319.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0319.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0319.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0319.allStagesChecked,?_,Step0319.initialMarginCheck⟩
    intro i
    change Step0319.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0319.stepData)[i.val]
    rw [← Step0319.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0315.stepData.coefficient 0 i=Step0315.inputData[i.val]
  exact Step0315.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.Block0003
