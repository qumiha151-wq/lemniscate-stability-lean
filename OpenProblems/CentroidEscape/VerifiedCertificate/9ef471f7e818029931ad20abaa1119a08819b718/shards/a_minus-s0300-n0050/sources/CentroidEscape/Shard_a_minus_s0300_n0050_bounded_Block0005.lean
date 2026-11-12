import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Step0325
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Step0326
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Step0327
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Step0328
import CentroidEscape.Shard_a_minus_s0300_n0050_bounded_Step0329

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0326.inputData=Step0325.endpointData := by decide +kernel

theorem glue1 : Step0327.inputData=Step0326.endpointData := by decide +kernel

theorem glue2 : Step0328.inputData=Step0327.endpointData := by decide +kernel

theorem glue3 : Step0329.inputData=Step0328.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0325.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0329.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0325.stepData
  | 1=>Step0326.stepData
  | 2=>Step0327.stepData
  | 3=>Step0328.stepData
  | 4=>Step0329.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0325.stepData=true ∧
      (∀ i : Fin 7, Step0326.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0325.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0325.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0325.allStagesChecked,?_,Step0325.initialMarginCheck⟩
    intro i
    rw [Step0326.inputCoefficient,← Step0325.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0326.stepData=true ∧
      (∀ i : Fin 7, Step0327.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0326.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0326.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0326.allStagesChecked,?_,Step0326.initialMarginCheck⟩
    intro i
    rw [Step0327.inputCoefficient,← Step0326.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0327.stepData=true ∧
      (∀ i : Fin 7, Step0328.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0327.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0327.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0327.allStagesChecked,?_,Step0327.initialMarginCheck⟩
    intro i
    rw [Step0328.inputCoefficient,← Step0327.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0328.stepData=true ∧
      (∀ i : Fin 7, Step0329.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0328.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0328.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0328.allStagesChecked,?_,Step0328.initialMarginCheck⟩
    intro i
    rw [Step0329.inputCoefficient,← Step0328.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0329.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0329.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0329.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0329.allStagesChecked,?_,Step0329.initialMarginCheck⟩
    intro i
    change Step0329.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0329.stepData)[i.val]
    rw [← Step0329.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0325.stepData.coefficient 0 i=Step0325.inputData[i.val]
  exact Step0325.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0300_n0050_bounded.Block0005
