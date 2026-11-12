import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Step0465
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Step0466
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Step0467
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Step0468
import CentroidEscape.Shard_b_plus_s0450_n0050_bounded_Step0469

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0466.inputData=Step0465.endpointData := by decide +kernel

theorem glue1 : Step0467.inputData=Step0466.endpointData := by decide +kernel

theorem glue2 : Step0468.inputData=Step0467.endpointData := by decide +kernel

theorem glue3 : Step0469.inputData=Step0468.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0465.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0469.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0465.stepData
  | 1=>Step0466.stepData
  | 2=>Step0467.stepData
  | 3=>Step0468.stepData
  | 4=>Step0469.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0465.stepData=true ∧
      (∀ i : Fin 7, Step0466.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0465.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0465.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0465.allStagesChecked,?_,Step0465.initialMarginCheck⟩
    intro i
    rw [Step0466.inputCoefficient,← Step0465.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0466.stepData=true ∧
      (∀ i : Fin 7, Step0467.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0466.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0466.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0466.allStagesChecked,?_,Step0466.initialMarginCheck⟩
    intro i
    rw [Step0467.inputCoefficient,← Step0466.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0467.stepData=true ∧
      (∀ i : Fin 7, Step0468.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0467.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0467.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0467.allStagesChecked,?_,Step0467.initialMarginCheck⟩
    intro i
    rw [Step0468.inputCoefficient,← Step0467.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0468.stepData=true ∧
      (∀ i : Fin 7, Step0469.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0468.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0468.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0468.allStagesChecked,?_,Step0468.initialMarginCheck⟩
    intro i
    rw [Step0469.inputCoefficient,← Step0468.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0469.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0469.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0469.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0469.allStagesChecked,?_,Step0469.initialMarginCheck⟩
    intro i
    change Step0469.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0469.stepData)[i.val]
    rw [← Step0469.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0465.stepData.coefficient 0 i=Step0465.inputData[i.val]
  exact Step0465.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0450_n0050_bounded.Block0003
