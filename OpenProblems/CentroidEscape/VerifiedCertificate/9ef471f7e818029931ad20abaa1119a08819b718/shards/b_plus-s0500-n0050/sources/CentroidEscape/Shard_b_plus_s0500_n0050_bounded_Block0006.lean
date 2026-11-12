import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0530
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0531
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0532
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0533
import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Step0534

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0531.inputData=Step0530.endpointData := by decide +kernel

theorem glue1 : Step0532.inputData=Step0531.endpointData := by decide +kernel

theorem glue2 : Step0533.inputData=Step0532.endpointData := by decide +kernel

theorem glue3 : Step0534.inputData=Step0533.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0530.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0534.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0530.stepData
  | 1=>Step0531.stepData
  | 2=>Step0532.stepData
  | 3=>Step0533.stepData
  | 4=>Step0534.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0530.stepData=true ∧
      (∀ i : Fin 7, Step0531.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0530.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0530.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0530.allStagesChecked,?_,Step0530.initialMarginCheck⟩
    intro i
    rw [Step0531.inputCoefficient,← Step0530.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0531.stepData=true ∧
      (∀ i : Fin 7, Step0532.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0531.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0531.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0531.allStagesChecked,?_,Step0531.initialMarginCheck⟩
    intro i
    rw [Step0532.inputCoefficient,← Step0531.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0532.stepData=true ∧
      (∀ i : Fin 7, Step0533.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0532.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0532.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0532.allStagesChecked,?_,Step0532.initialMarginCheck⟩
    intro i
    rw [Step0533.inputCoefficient,← Step0532.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0533.stepData=true ∧
      (∀ i : Fin 7, Step0534.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0533.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0533.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0533.allStagesChecked,?_,Step0533.initialMarginCheck⟩
    intro i
    rw [Step0534.inputCoefficient,← Step0533.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0534.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0534.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0534.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0534.allStagesChecked,?_,Step0534.initialMarginCheck⟩
    intro i
    change Step0534.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0534.stepData)[i.val]
    rw [← Step0534.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0530.stepData.coefficient 0 i=Step0530.inputData[i.val]
  exact Step0530.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Block0006
