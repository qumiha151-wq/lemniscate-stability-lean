import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0510
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0511
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0512
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0513
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0514

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0511.inputData=Step0510.endpointData := by decide +kernel

theorem glue1 : Step0512.inputData=Step0511.endpointData := by decide +kernel

theorem glue2 : Step0513.inputData=Step0512.endpointData := by decide +kernel

theorem glue3 : Step0514.inputData=Step0513.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0510.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0514.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0510.stepData
  | 1=>Step0511.stepData
  | 2=>Step0512.stepData
  | 3=>Step0513.stepData
  | 4=>Step0514.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0510.stepData=true ∧
      (∀ i : Fin 7, Step0511.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0510.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0510.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0510.allStagesChecked,?_,Step0510.initialMarginCheck⟩
    intro i
    rw [Step0511.inputCoefficient,← Step0510.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0511.stepData=true ∧
      (∀ i : Fin 7, Step0512.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0511.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0511.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0511.allStagesChecked,?_,Step0511.initialMarginCheck⟩
    intro i
    rw [Step0512.inputCoefficient,← Step0511.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0512.stepData=true ∧
      (∀ i : Fin 7, Step0513.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0512.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0512.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0512.allStagesChecked,?_,Step0512.initialMarginCheck⟩
    intro i
    rw [Step0513.inputCoefficient,← Step0512.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0513.stepData=true ∧
      (∀ i : Fin 7, Step0514.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0513.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0513.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0513.allStagesChecked,?_,Step0513.initialMarginCheck⟩
    intro i
    rw [Step0514.inputCoefficient,← Step0513.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0514.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0514.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0514.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0514.allStagesChecked,?_,Step0514.initialMarginCheck⟩
    intro i
    change Step0514.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0514.stepData)[i.val]
    rw [← Step0514.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0510.stepData.coefficient 0 i=Step0510.inputData[i.val]
  exact Step0510.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Block0002
