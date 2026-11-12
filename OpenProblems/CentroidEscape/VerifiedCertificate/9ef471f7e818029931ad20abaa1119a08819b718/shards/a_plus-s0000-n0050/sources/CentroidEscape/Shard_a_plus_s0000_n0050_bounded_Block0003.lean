import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0015
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0016
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0017
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0018
import CentroidEscape.Shard_a_plus_s0000_n0050_bounded_Step0019

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0016.inputData=Step0015.endpointData := by decide +kernel

theorem glue1 : Step0017.inputData=Step0016.endpointData := by decide +kernel

theorem glue2 : Step0018.inputData=Step0017.endpointData := by decide +kernel

theorem glue3 : Step0019.inputData=Step0018.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0015.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0019.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0015.stepData
  | 1=>Step0016.stepData
  | 2=>Step0017.stepData
  | 3=>Step0018.stepData
  | 4=>Step0019.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0015.stepData=true ∧
      (∀ i : Fin 7, Step0016.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0015.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0015.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0015.allStagesChecked,?_,Step0015.initialMarginCheck⟩
    intro i
    rw [Step0016.inputCoefficient,← Step0015.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0016.stepData=true ∧
      (∀ i : Fin 7, Step0017.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0016.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0016.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0016.allStagesChecked,?_,Step0016.initialMarginCheck⟩
    intro i
    rw [Step0017.inputCoefficient,← Step0016.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0017.stepData=true ∧
      (∀ i : Fin 7, Step0018.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0017.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0017.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0017.allStagesChecked,?_,Step0017.initialMarginCheck⟩
    intro i
    rw [Step0018.inputCoefficient,← Step0017.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0018.stepData=true ∧
      (∀ i : Fin 7, Step0019.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0018.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0018.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0018.allStagesChecked,?_,Step0018.initialMarginCheck⟩
    intro i
    rw [Step0019.inputCoefficient,← Step0018.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0019.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0019.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0019.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0019.allStagesChecked,?_,Step0019.initialMarginCheck⟩
    intro i
    change Step0019.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0019.stepData)[i.val]
    rw [← Step0019.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0015.stepData.coefficient 0 i=Step0015.inputData[i.val]
  exact Step0015.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0000_n0050_bounded.Block0003
