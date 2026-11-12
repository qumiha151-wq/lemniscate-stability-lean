import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0585
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0586
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0587
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0588
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0589

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0586.inputData=Step0585.endpointData := by decide +kernel

theorem glue1 : Step0587.inputData=Step0586.endpointData := by decide +kernel

theorem glue2 : Step0588.inputData=Step0587.endpointData := by decide +kernel

theorem glue3 : Step0589.inputData=Step0588.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0585.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0589.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0585.stepData
  | 1=>Step0586.stepData
  | 2=>Step0587.stepData
  | 3=>Step0588.stepData
  | 4=>Step0589.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0585.stepData=true ∧
      (∀ i : Fin 7, Step0586.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0585.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0585.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0585.allStagesChecked,?_,Step0585.initialMarginCheck⟩
    intro i
    rw [Step0586.inputCoefficient,← Step0585.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0586.stepData=true ∧
      (∀ i : Fin 7, Step0587.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0586.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0586.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0586.allStagesChecked,?_,Step0586.initialMarginCheck⟩
    intro i
    rw [Step0587.inputCoefficient,← Step0586.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0587.stepData=true ∧
      (∀ i : Fin 7, Step0588.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0587.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0587.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0587.allStagesChecked,?_,Step0587.initialMarginCheck⟩
    intro i
    rw [Step0588.inputCoefficient,← Step0587.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0588.stepData=true ∧
      (∀ i : Fin 7, Step0589.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0588.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0588.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0588.allStagesChecked,?_,Step0588.initialMarginCheck⟩
    intro i
    rw [Step0589.inputCoefficient,← Step0588.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0589.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0589.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0589.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0589.allStagesChecked,?_,Step0589.initialMarginCheck⟩
    intro i
    change Step0589.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0589.stepData)[i.val]
    rw [← Step0589.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0585.stepData.coefficient 0 i=Step0585.inputData[i.val]
  exact Step0585.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Block0007
