import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0370
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0371
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0372
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0373
import CentroidEscape.Shard_center_s0350_n0050_bounded_Step0374

namespace CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0371.inputData=Step0370.endpointData := by decide +kernel

theorem glue1 : Step0372.inputData=Step0371.endpointData := by decide +kernel

theorem glue2 : Step0373.inputData=Step0372.endpointData := by decide +kernel

theorem glue3 : Step0374.inputData=Step0373.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0370.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0374.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0370.stepData
  | 1=>Step0371.stepData
  | 2=>Step0372.stepData
  | 3=>Step0373.stepData
  | 4=>Step0374.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0370.stepData=true ∧
      (∀ i : Fin 7, Step0371.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0370.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0370.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0370.allStagesChecked,?_,Step0370.initialMarginCheck⟩
    intro i
    rw [Step0371.inputCoefficient,← Step0370.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0371.stepData=true ∧
      (∀ i : Fin 7, Step0372.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0371.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0371.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0371.allStagesChecked,?_,Step0371.initialMarginCheck⟩
    intro i
    rw [Step0372.inputCoefficient,← Step0371.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0372.stepData=true ∧
      (∀ i : Fin 7, Step0373.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0372.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0372.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0372.allStagesChecked,?_,Step0372.initialMarginCheck⟩
    intro i
    rw [Step0373.inputCoefficient,← Step0372.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0373.stepData=true ∧
      (∀ i : Fin 7, Step0374.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0373.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0373.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0373.allStagesChecked,?_,Step0373.initialMarginCheck⟩
    intro i
    rw [Step0374.inputCoefficient,← Step0373.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0374.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0374.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0374.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0374.allStagesChecked,?_,Step0374.initialMarginCheck⟩
    intro i
    change Step0374.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0374.stepData)[i.val]
    rw [← Step0374.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0370.stepData.coefficient 0 i=Step0370.inputData[i.val]
  exact Step0370.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0350_n0050_bounded.Block0004
