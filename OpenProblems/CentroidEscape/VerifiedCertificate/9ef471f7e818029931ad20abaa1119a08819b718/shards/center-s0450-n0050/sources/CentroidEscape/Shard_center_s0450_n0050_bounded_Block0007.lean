import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0450_n0050_bounded_Step0485
import CentroidEscape.Shard_center_s0450_n0050_bounded_Step0486
import CentroidEscape.Shard_center_s0450_n0050_bounded_Step0487
import CentroidEscape.Shard_center_s0450_n0050_bounded_Step0488
import CentroidEscape.Shard_center_s0450_n0050_bounded_Step0489

namespace CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0486.inputData=Step0485.endpointData := by decide +kernel

theorem glue1 : Step0487.inputData=Step0486.endpointData := by decide +kernel

theorem glue2 : Step0488.inputData=Step0487.endpointData := by decide +kernel

theorem glue3 : Step0489.inputData=Step0488.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0485.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0489.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0485.stepData
  | 1=>Step0486.stepData
  | 2=>Step0487.stepData
  | 3=>Step0488.stepData
  | 4=>Step0489.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0485.stepData=true ∧
      (∀ i : Fin 7, Step0486.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0485.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0485.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0485.allStagesChecked,?_,Step0485.initialMarginCheck⟩
    intro i
    rw [Step0486.inputCoefficient,← Step0485.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0486.stepData=true ∧
      (∀ i : Fin 7, Step0487.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0486.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0486.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0486.allStagesChecked,?_,Step0486.initialMarginCheck⟩
    intro i
    rw [Step0487.inputCoefficient,← Step0486.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0487.stepData=true ∧
      (∀ i : Fin 7, Step0488.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0487.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0487.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0487.allStagesChecked,?_,Step0487.initialMarginCheck⟩
    intro i
    rw [Step0488.inputCoefficient,← Step0487.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0488.stepData=true ∧
      (∀ i : Fin 7, Step0489.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0488.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0488.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0488.allStagesChecked,?_,Step0488.initialMarginCheck⟩
    intro i
    rw [Step0489.inputCoefficient,← Step0488.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0489.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0489.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0489.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0489.allStagesChecked,?_,Step0489.initialMarginCheck⟩
    intro i
    change Step0489.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0489.stepData)[i.val]
    rw [← Step0489.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0485.stepData.coefficient 0 i=Step0485.inputData[i.val]
  exact Step0485.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0450_n0050_bounded.Block0007
