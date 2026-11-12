import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0310
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0311
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0312
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0313
import CentroidEscape.Shard_b_minus_s0300_n0050_bounded_Step0314

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0311.inputData=Step0310.endpointData := by decide +kernel

theorem glue1 : Step0312.inputData=Step0311.endpointData := by decide +kernel

theorem glue2 : Step0313.inputData=Step0312.endpointData := by decide +kernel

theorem glue3 : Step0314.inputData=Step0313.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0310.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0314.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0310.stepData
  | 1=>Step0311.stepData
  | 2=>Step0312.stepData
  | 3=>Step0313.stepData
  | 4=>Step0314.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0310.stepData=true ∧
      (∀ i : Fin 7, Step0311.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0310.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0310.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0310.allStagesChecked,?_,Step0310.initialMarginCheck⟩
    intro i
    rw [Step0311.inputCoefficient,← Step0310.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0311.stepData=true ∧
      (∀ i : Fin 7, Step0312.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0311.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0311.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0311.allStagesChecked,?_,Step0311.initialMarginCheck⟩
    intro i
    rw [Step0312.inputCoefficient,← Step0311.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0312.stepData=true ∧
      (∀ i : Fin 7, Step0313.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0312.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0312.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0312.allStagesChecked,?_,Step0312.initialMarginCheck⟩
    intro i
    rw [Step0313.inputCoefficient,← Step0312.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0313.stepData=true ∧
      (∀ i : Fin 7, Step0314.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0313.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0313.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0313.allStagesChecked,?_,Step0313.initialMarginCheck⟩
    intro i
    rw [Step0314.inputCoefficient,← Step0313.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0314.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0314.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0314.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0314.allStagesChecked,?_,Step0314.initialMarginCheck⟩
    intro i
    change Step0314.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0314.stepData)[i.val]
    rw [← Step0314.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0310.stepData.coefficient 0 i=Step0310.inputData[i.val]
  exact Step0310.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0300_n0050_bounded.Block0002
