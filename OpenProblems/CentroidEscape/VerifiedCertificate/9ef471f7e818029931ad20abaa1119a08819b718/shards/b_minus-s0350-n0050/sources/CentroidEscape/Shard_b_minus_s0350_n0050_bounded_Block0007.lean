import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0385
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0386
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0387
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0388
import CentroidEscape.Shard_b_minus_s0350_n0050_bounded_Step0389

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0386.inputData=Step0385.endpointData := by decide +kernel

theorem glue1 : Step0387.inputData=Step0386.endpointData := by decide +kernel

theorem glue2 : Step0388.inputData=Step0387.endpointData := by decide +kernel

theorem glue3 : Step0389.inputData=Step0388.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0385.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0389.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0385.stepData
  | 1=>Step0386.stepData
  | 2=>Step0387.stepData
  | 3=>Step0388.stepData
  | 4=>Step0389.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0385.stepData=true ∧
      (∀ i : Fin 7, Step0386.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0385.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0385.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0385.allStagesChecked,?_,Step0385.initialMarginCheck⟩
    intro i
    rw [Step0386.inputCoefficient,← Step0385.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0386.stepData=true ∧
      (∀ i : Fin 7, Step0387.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0386.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0386.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0386.allStagesChecked,?_,Step0386.initialMarginCheck⟩
    intro i
    rw [Step0387.inputCoefficient,← Step0386.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0387.stepData=true ∧
      (∀ i : Fin 7, Step0388.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0387.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0387.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0387.allStagesChecked,?_,Step0387.initialMarginCheck⟩
    intro i
    rw [Step0388.inputCoefficient,← Step0387.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0388.stepData=true ∧
      (∀ i : Fin 7, Step0389.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0388.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0388.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0388.allStagesChecked,?_,Step0388.initialMarginCheck⟩
    intro i
    rw [Step0389.inputCoefficient,← Step0388.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0389.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0389.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0389.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0389.allStagesChecked,?_,Step0389.initialMarginCheck⟩
    intro i
    change Step0389.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0389.stepData)[i.val]
    rw [← Step0389.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0385.stepData.coefficient 0 i=Step0385.inputData[i.val]
  exact Step0385.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0350_n0050_bounded.Block0007
