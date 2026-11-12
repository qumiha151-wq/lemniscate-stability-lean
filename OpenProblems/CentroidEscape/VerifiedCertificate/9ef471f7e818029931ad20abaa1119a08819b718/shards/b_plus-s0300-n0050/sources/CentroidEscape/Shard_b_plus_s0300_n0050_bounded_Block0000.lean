import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0300
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0301
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0302
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0303
import CentroidEscape.Shard_b_plus_s0300_n0050_bounded_Step0304

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0301.inputData=Step0300.endpointData := by decide +kernel

theorem glue1 : Step0302.inputData=Step0301.endpointData := by decide +kernel

theorem glue2 : Step0303.inputData=Step0302.endpointData := by decide +kernel

theorem glue3 : Step0304.inputData=Step0303.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0300.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0304.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0300.stepData
  | 1=>Step0301.stepData
  | 2=>Step0302.stepData
  | 3=>Step0303.stepData
  | 4=>Step0304.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0300.stepData=true ∧
      (∀ i : Fin 7, Step0301.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0300.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0300.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0300.allStagesChecked,?_,Step0300.initialMarginCheck⟩
    intro i
    rw [Step0301.inputCoefficient,← Step0300.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0301.stepData=true ∧
      (∀ i : Fin 7, Step0302.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0301.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0301.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0301.allStagesChecked,?_,Step0301.initialMarginCheck⟩
    intro i
    rw [Step0302.inputCoefficient,← Step0301.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0302.stepData=true ∧
      (∀ i : Fin 7, Step0303.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0302.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0302.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0302.allStagesChecked,?_,Step0302.initialMarginCheck⟩
    intro i
    rw [Step0303.inputCoefficient,← Step0302.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0303.stepData=true ∧
      (∀ i : Fin 7, Step0304.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0303.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0303.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0303.allStagesChecked,?_,Step0303.initialMarginCheck⟩
    intro i
    rw [Step0304.inputCoefficient,← Step0303.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0304.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0304.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0304.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0304.allStagesChecked,?_,Step0304.initialMarginCheck⟩
    intro i
    change Step0304.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0304.stepData)[i.val]
    rw [← Step0304.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0300.stepData.coefficient 0 i=Step0300.inputData[i.val]
  exact Step0300.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0300_n0050_bounded.Block0000
