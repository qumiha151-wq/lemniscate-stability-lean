import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0450_n0050_bounded_Step0495
import CentroidEscape.Shard_a_plus_s0450_n0050_bounded_Step0496
import CentroidEscape.Shard_a_plus_s0450_n0050_bounded_Step0497
import CentroidEscape.Shard_a_plus_s0450_n0050_bounded_Step0498
import CentroidEscape.Shard_a_plus_s0450_n0050_bounded_Step0499

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0450_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0496.inputData=Step0495.endpointData := by decide +kernel

theorem glue1 : Step0497.inputData=Step0496.endpointData := by decide +kernel

theorem glue2 : Step0498.inputData=Step0497.endpointData := by decide +kernel

theorem glue3 : Step0499.inputData=Step0498.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0495.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0499.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0495.stepData
  | 1=>Step0496.stepData
  | 2=>Step0497.stepData
  | 3=>Step0498.stepData
  | 4=>Step0499.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0495.stepData=true ∧
      (∀ i : Fin 7, Step0496.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0495.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0495.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0495.allStagesChecked,?_,Step0495.initialMarginCheck⟩
    intro i
    rw [Step0496.inputCoefficient,← Step0495.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0496.stepData=true ∧
      (∀ i : Fin 7, Step0497.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0496.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0496.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0496.allStagesChecked,?_,Step0496.initialMarginCheck⟩
    intro i
    rw [Step0497.inputCoefficient,← Step0496.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0497.stepData=true ∧
      (∀ i : Fin 7, Step0498.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0497.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0497.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0497.allStagesChecked,?_,Step0497.initialMarginCheck⟩
    intro i
    rw [Step0498.inputCoefficient,← Step0497.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0498.stepData=true ∧
      (∀ i : Fin 7, Step0499.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0498.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0498.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0498.allStagesChecked,?_,Step0498.initialMarginCheck⟩
    intro i
    rw [Step0499.inputCoefficient,← Step0498.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0499.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0499.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0499.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0499.allStagesChecked,?_,Step0499.initialMarginCheck⟩
    intro i
    change Step0499.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0499.stepData)[i.val]
    rw [← Step0499.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0495.stepData.coefficient 0 i=Step0495.inputData[i.val]
  exact Step0495.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0450_n0050_bounded.Block0009
