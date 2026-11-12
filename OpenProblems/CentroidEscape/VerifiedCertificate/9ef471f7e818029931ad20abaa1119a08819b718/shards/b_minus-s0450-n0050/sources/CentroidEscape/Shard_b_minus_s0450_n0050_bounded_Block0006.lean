import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0480
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0481
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0482
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0483
import CentroidEscape.Shard_b_minus_s0450_n0050_bounded_Step0484

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Block0006
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0481.inputData=Step0480.endpointData := by decide +kernel

theorem glue1 : Step0482.inputData=Step0481.endpointData := by decide +kernel

theorem glue2 : Step0483.inputData=Step0482.endpointData := by decide +kernel

theorem glue3 : Step0484.inputData=Step0483.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0480.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0484.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0480.stepData
  | 1=>Step0481.stepData
  | 2=>Step0482.stepData
  | 3=>Step0483.stepData
  | 4=>Step0484.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0480.stepData=true ∧
      (∀ i : Fin 7, Step0481.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0480.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0480.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0480.allStagesChecked,?_,Step0480.initialMarginCheck⟩
    intro i
    rw [Step0481.inputCoefficient,← Step0480.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0481.stepData=true ∧
      (∀ i : Fin 7, Step0482.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0481.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0481.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0481.allStagesChecked,?_,Step0481.initialMarginCheck⟩
    intro i
    rw [Step0482.inputCoefficient,← Step0481.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0482.stepData=true ∧
      (∀ i : Fin 7, Step0483.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0482.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0482.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0482.allStagesChecked,?_,Step0482.initialMarginCheck⟩
    intro i
    rw [Step0483.inputCoefficient,← Step0482.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0483.stepData=true ∧
      (∀ i : Fin 7, Step0484.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0483.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0483.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0483.allStagesChecked,?_,Step0483.initialMarginCheck⟩
    intro i
    rw [Step0484.inputCoefficient,← Step0483.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0484.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0484.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0484.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0484.allStagesChecked,?_,Step0484.initialMarginCheck⟩
    intro i
    change Step0484.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0484.stepData)[i.val]
    rw [← Step0484.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0480.stepData.coefficient 0 i=Step0480.inputData[i.val]
  exact Step0480.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0450_n0050_bounded.Block0006
