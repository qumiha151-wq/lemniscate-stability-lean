import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0150_n0050_bounded_Step0155
import CentroidEscape.Shard_a_plus_s0150_n0050_bounded_Step0156
import CentroidEscape.Shard_a_plus_s0150_n0050_bounded_Step0157
import CentroidEscape.Shard_a_plus_s0150_n0050_bounded_Step0158
import CentroidEscape.Shard_a_plus_s0150_n0050_bounded_Step0159

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0150_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0156.inputData=Step0155.endpointData := by decide +kernel

theorem glue1 : Step0157.inputData=Step0156.endpointData := by decide +kernel

theorem glue2 : Step0158.inputData=Step0157.endpointData := by decide +kernel

theorem glue3 : Step0159.inputData=Step0158.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0155.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0159.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0155.stepData
  | 1=>Step0156.stepData
  | 2=>Step0157.stepData
  | 3=>Step0158.stepData
  | 4=>Step0159.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0155.stepData=true ∧
      (∀ i : Fin 7, Step0156.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0155.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0155.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0155.allStagesChecked,?_,Step0155.initialMarginCheck⟩
    intro i
    rw [Step0156.inputCoefficient,← Step0155.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0156.stepData=true ∧
      (∀ i : Fin 7, Step0157.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0156.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0156.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0156.allStagesChecked,?_,Step0156.initialMarginCheck⟩
    intro i
    rw [Step0157.inputCoefficient,← Step0156.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0157.stepData=true ∧
      (∀ i : Fin 7, Step0158.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0157.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0157.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0157.allStagesChecked,?_,Step0157.initialMarginCheck⟩
    intro i
    rw [Step0158.inputCoefficient,← Step0157.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0158.stepData=true ∧
      (∀ i : Fin 7, Step0159.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0158.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0158.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0158.allStagesChecked,?_,Step0158.initialMarginCheck⟩
    intro i
    rw [Step0159.inputCoefficient,← Step0158.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0159.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0159.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0159.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0159.allStagesChecked,?_,Step0159.initialMarginCheck⟩
    intro i
    change Step0159.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0159.stepData)[i.val]
    rw [← Step0159.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0155.stepData.coefficient 0 i=Step0155.inputData[i.val]
  exact Step0155.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0150_n0050_bounded.Block0001
