import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0475
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0476
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0477
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0478
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0479

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0476.inputData=Step0475.endpointData := by decide +kernel

theorem glue1 : Step0477.inputData=Step0476.endpointData := by decide +kernel

theorem glue2 : Step0478.inputData=Step0477.endpointData := by decide +kernel

theorem glue3 : Step0479.inputData=Step0478.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0475.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0479.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0475.stepData
  | 1=>Step0476.stepData
  | 2=>Step0477.stepData
  | 3=>Step0478.stepData
  | 4=>Step0479.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0475.stepData=true ∧
      (∀ i : Fin 7, Step0476.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0475.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0475.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0475.allStagesChecked,?_,Step0475.initialMarginCheck⟩
    intro i
    rw [Step0476.inputCoefficient,← Step0475.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0476.stepData=true ∧
      (∀ i : Fin 7, Step0477.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0476.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0476.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0476.allStagesChecked,?_,Step0476.initialMarginCheck⟩
    intro i
    rw [Step0477.inputCoefficient,← Step0476.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0477.stepData=true ∧
      (∀ i : Fin 7, Step0478.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0477.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0477.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0477.allStagesChecked,?_,Step0477.initialMarginCheck⟩
    intro i
    rw [Step0478.inputCoefficient,← Step0477.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0478.stepData=true ∧
      (∀ i : Fin 7, Step0479.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0478.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0478.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0478.allStagesChecked,?_,Step0478.initialMarginCheck⟩
    intro i
    rw [Step0479.inputCoefficient,← Step0478.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0479.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0479.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0479.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0479.allStagesChecked,?_,Step0479.initialMarginCheck⟩
    intro i
    change Step0479.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0479.stepData)[i.val]
    rw [← Step0479.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0475.stepData.coefficient 0 i=Step0475.inputData[i.val]
  exact Step0475.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Block0005
