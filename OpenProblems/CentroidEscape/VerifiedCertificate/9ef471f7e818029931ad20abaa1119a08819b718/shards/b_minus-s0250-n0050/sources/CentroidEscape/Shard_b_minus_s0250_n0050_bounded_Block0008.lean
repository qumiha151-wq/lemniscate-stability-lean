import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Step0290
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Step0291
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Step0292
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Step0293
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Step0294

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0291.inputData=Step0290.endpointData := by decide +kernel

theorem glue1 : Step0292.inputData=Step0291.endpointData := by decide +kernel

theorem glue2 : Step0293.inputData=Step0292.endpointData := by decide +kernel

theorem glue3 : Step0294.inputData=Step0293.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0290.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0294.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0290.stepData
  | 1=>Step0291.stepData
  | 2=>Step0292.stepData
  | 3=>Step0293.stepData
  | 4=>Step0294.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0290.stepData=true ∧
      (∀ i : Fin 7, Step0291.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0290.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0290.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0290.allStagesChecked,?_,Step0290.initialMarginCheck⟩
    intro i
    rw [Step0291.inputCoefficient,← Step0290.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0291.stepData=true ∧
      (∀ i : Fin 7, Step0292.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0291.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0291.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0291.allStagesChecked,?_,Step0291.initialMarginCheck⟩
    intro i
    rw [Step0292.inputCoefficient,← Step0291.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0292.stepData=true ∧
      (∀ i : Fin 7, Step0293.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0292.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0292.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0292.allStagesChecked,?_,Step0292.initialMarginCheck⟩
    intro i
    rw [Step0293.inputCoefficient,← Step0292.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0293.stepData=true ∧
      (∀ i : Fin 7, Step0294.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0293.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0293.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0293.allStagesChecked,?_,Step0293.initialMarginCheck⟩
    intro i
    rw [Step0294.inputCoefficient,← Step0293.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0294.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0294.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0294.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0294.allStagesChecked,?_,Step0294.initialMarginCheck⟩
    intro i
    change Step0294.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0294.stepData)[i.val]
    rw [← Step0294.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0290.stepData.coefficient 0 i=Step0290.inputData[i.val]
  exact Step0290.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.Block0008
