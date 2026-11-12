import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0410
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0411
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0412
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0413
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0414

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0411.inputData=Step0410.endpointData := by decide +kernel

theorem glue1 : Step0412.inputData=Step0411.endpointData := by decide +kernel

theorem glue2 : Step0413.inputData=Step0412.endpointData := by decide +kernel

theorem glue3 : Step0414.inputData=Step0413.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0410.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0414.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0410.stepData
  | 1=>Step0411.stepData
  | 2=>Step0412.stepData
  | 3=>Step0413.stepData
  | 4=>Step0414.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0410.stepData=true ∧
      (∀ i : Fin 7, Step0411.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0410.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0410.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0410.allStagesChecked,?_,Step0410.initialMarginCheck⟩
    intro i
    rw [Step0411.inputCoefficient,← Step0410.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0411.stepData=true ∧
      (∀ i : Fin 7, Step0412.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0411.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0411.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0411.allStagesChecked,?_,Step0411.initialMarginCheck⟩
    intro i
    rw [Step0412.inputCoefficient,← Step0411.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0412.stepData=true ∧
      (∀ i : Fin 7, Step0413.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0412.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0412.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0412.allStagesChecked,?_,Step0412.initialMarginCheck⟩
    intro i
    rw [Step0413.inputCoefficient,← Step0412.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0413.stepData=true ∧
      (∀ i : Fin 7, Step0414.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0413.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0413.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0413.allStagesChecked,?_,Step0413.initialMarginCheck⟩
    intro i
    rw [Step0414.inputCoefficient,← Step0413.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0414.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0414.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0414.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0414.allStagesChecked,?_,Step0414.initialMarginCheck⟩
    intro i
    change Step0414.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0414.stepData)[i.val]
    rw [← Step0414.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0410.stepData.coefficient 0 i=Step0410.inputData[i.val]
  exact Step0410.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Block0002
