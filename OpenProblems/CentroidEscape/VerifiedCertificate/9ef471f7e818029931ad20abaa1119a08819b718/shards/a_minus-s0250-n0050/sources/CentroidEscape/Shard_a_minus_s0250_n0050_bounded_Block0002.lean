import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0260
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0261
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0262
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0263
import CentroidEscape.Shard_a_minus_s0250_n0050_bounded_Step0264

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0261.inputData=Step0260.endpointData := by decide +kernel

theorem glue1 : Step0262.inputData=Step0261.endpointData := by decide +kernel

theorem glue2 : Step0263.inputData=Step0262.endpointData := by decide +kernel

theorem glue3 : Step0264.inputData=Step0263.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0260.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0264.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0260.stepData
  | 1=>Step0261.stepData
  | 2=>Step0262.stepData
  | 3=>Step0263.stepData
  | 4=>Step0264.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0260.stepData=true ∧
      (∀ i : Fin 7, Step0261.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0260.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0260.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0260.allStagesChecked,?_,Step0260.initialMarginCheck⟩
    intro i
    rw [Step0261.inputCoefficient,← Step0260.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0261.stepData=true ∧
      (∀ i : Fin 7, Step0262.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0261.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0261.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0261.allStagesChecked,?_,Step0261.initialMarginCheck⟩
    intro i
    rw [Step0262.inputCoefficient,← Step0261.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0262.stepData=true ∧
      (∀ i : Fin 7, Step0263.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0262.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0262.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0262.allStagesChecked,?_,Step0262.initialMarginCheck⟩
    intro i
    rw [Step0263.inputCoefficient,← Step0262.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0263.stepData=true ∧
      (∀ i : Fin 7, Step0264.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0263.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0263.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0263.allStagesChecked,?_,Step0263.initialMarginCheck⟩
    intro i
    rw [Step0264.inputCoefficient,← Step0263.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0264.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0264.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0264.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0264.allStagesChecked,?_,Step0264.initialMarginCheck⟩
    intro i
    change Step0264.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0264.stepData)[i.val]
    rw [← Step0264.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0260.stepData.coefficient 0 i=Step0260.inputData[i.val]
  exact Step0260.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0250_n0050_bounded.Block0002
