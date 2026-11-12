import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0520
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0521
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0522
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0523
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Step0524

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0521.inputData=Step0520.endpointData := by decide +kernel

theorem glue1 : Step0522.inputData=Step0521.endpointData := by decide +kernel

theorem glue2 : Step0523.inputData=Step0522.endpointData := by decide +kernel

theorem glue3 : Step0524.inputData=Step0523.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0520.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0524.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0520.stepData
  | 1=>Step0521.stepData
  | 2=>Step0522.stepData
  | 3=>Step0523.stepData
  | 4=>Step0524.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0520.stepData=true ∧
      (∀ i : Fin 7, Step0521.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0520.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0520.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0520.allStagesChecked,?_,Step0520.initialMarginCheck⟩
    intro i
    rw [Step0521.inputCoefficient,← Step0520.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0521.stepData=true ∧
      (∀ i : Fin 7, Step0522.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0521.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0521.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0521.allStagesChecked,?_,Step0521.initialMarginCheck⟩
    intro i
    rw [Step0522.inputCoefficient,← Step0521.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0522.stepData=true ∧
      (∀ i : Fin 7, Step0523.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0522.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0522.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0522.allStagesChecked,?_,Step0522.initialMarginCheck⟩
    intro i
    rw [Step0523.inputCoefficient,← Step0522.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0523.stepData=true ∧
      (∀ i : Fin 7, Step0524.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0523.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0523.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0523.allStagesChecked,?_,Step0523.initialMarginCheck⟩
    intro i
    rw [Step0524.inputCoefficient,← Step0523.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0524.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0524.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0524.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0524.allStagesChecked,?_,Step0524.initialMarginCheck⟩
    intro i
    change Step0524.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0524.stepData)[i.val]
    rw [← Step0524.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0520.stepData.coefficient 0 i=Step0520.inputData[i.val]
  exact Step0520.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Block0004
