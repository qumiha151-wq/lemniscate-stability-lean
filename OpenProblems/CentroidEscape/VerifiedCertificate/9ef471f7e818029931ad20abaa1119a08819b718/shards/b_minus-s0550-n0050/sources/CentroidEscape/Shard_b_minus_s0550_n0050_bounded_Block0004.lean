import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0550_n0050_bounded_Step0570
import CentroidEscape.Shard_b_minus_s0550_n0050_bounded_Step0571
import CentroidEscape.Shard_b_minus_s0550_n0050_bounded_Step0572
import CentroidEscape.Shard_b_minus_s0550_n0050_bounded_Step0573
import CentroidEscape.Shard_b_minus_s0550_n0050_bounded_Step0574

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0550_n0050_bounded.Block0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0571.inputData=Step0570.endpointData := by decide +kernel

theorem glue1 : Step0572.inputData=Step0571.endpointData := by decide +kernel

theorem glue2 : Step0573.inputData=Step0572.endpointData := by decide +kernel

theorem glue3 : Step0574.inputData=Step0573.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0570.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0574.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0570.stepData
  | 1=>Step0571.stepData
  | 2=>Step0572.stepData
  | 3=>Step0573.stepData
  | 4=>Step0574.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0570.stepData=true ∧
      (∀ i : Fin 7, Step0571.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0570.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0570.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0570.allStagesChecked,?_,Step0570.initialMarginCheck⟩
    intro i
    rw [Step0571.inputCoefficient,← Step0570.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0571.stepData=true ∧
      (∀ i : Fin 7, Step0572.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0571.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0571.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0571.allStagesChecked,?_,Step0571.initialMarginCheck⟩
    intro i
    rw [Step0572.inputCoefficient,← Step0571.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0572.stepData=true ∧
      (∀ i : Fin 7, Step0573.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0572.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0572.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0572.allStagesChecked,?_,Step0572.initialMarginCheck⟩
    intro i
    rw [Step0573.inputCoefficient,← Step0572.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0573.stepData=true ∧
      (∀ i : Fin 7, Step0574.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0573.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0573.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0573.allStagesChecked,?_,Step0573.initialMarginCheck⟩
    intro i
    rw [Step0574.inputCoefficient,← Step0573.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0574.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0574.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0574.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0574.allStagesChecked,?_,Step0574.initialMarginCheck⟩
    intro i
    change Step0574.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0574.stepData)[i.val]
    rw [← Step0574.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0570.stepData.coefficient 0 i=Step0570.inputData[i.val]
  exact Step0570.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0550_n0050_bounded.Block0004
