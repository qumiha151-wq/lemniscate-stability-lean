import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0305
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0306
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0307
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0308
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0309

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0306.inputData=Step0305.endpointData := by decide +kernel

theorem glue1 : Step0307.inputData=Step0306.endpointData := by decide +kernel

theorem glue2 : Step0308.inputData=Step0307.endpointData := by decide +kernel

theorem glue3 : Step0309.inputData=Step0308.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0305.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0309.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0305.stepData
  | 1=>Step0306.stepData
  | 2=>Step0307.stepData
  | 3=>Step0308.stepData
  | 4=>Step0309.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0305.stepData=true ∧
      (∀ i : Fin 7, Step0306.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0305.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0305.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0305.allStagesChecked,?_,Step0305.initialMarginCheck⟩
    intro i
    rw [Step0306.inputCoefficient,← Step0305.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0306.stepData=true ∧
      (∀ i : Fin 7, Step0307.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0306.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0306.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0306.allStagesChecked,?_,Step0306.initialMarginCheck⟩
    intro i
    rw [Step0307.inputCoefficient,← Step0306.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0307.stepData=true ∧
      (∀ i : Fin 7, Step0308.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0307.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0307.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0307.allStagesChecked,?_,Step0307.initialMarginCheck⟩
    intro i
    rw [Step0308.inputCoefficient,← Step0307.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0308.stepData=true ∧
      (∀ i : Fin 7, Step0309.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0308.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0308.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0308.allStagesChecked,?_,Step0308.initialMarginCheck⟩
    intro i
    rw [Step0309.inputCoefficient,← Step0308.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0309.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0309.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0309.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0309.allStagesChecked,?_,Step0309.initialMarginCheck⟩
    intro i
    change Step0309.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0309.stepData)[i.val]
    rw [← Step0309.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0305.stepData.coefficient 0 i=Step0305.inputData[i.val]
  exact Step0305.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Block0001
