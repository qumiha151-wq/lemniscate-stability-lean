import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0600
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0601
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0602
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0603
import CentroidEscape.Shard_center_s0600_n0050_bounded_Step0604

namespace CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0601.inputData=Step0600.endpointData := by decide +kernel

theorem glue1 : Step0602.inputData=Step0601.endpointData := by decide +kernel

theorem glue2 : Step0603.inputData=Step0602.endpointData := by decide +kernel

theorem glue3 : Step0604.inputData=Step0603.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0600.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0604.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0600.stepData
  | 1=>Step0601.stepData
  | 2=>Step0602.stepData
  | 3=>Step0603.stepData
  | 4=>Step0604.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0600.stepData=true ∧
      (∀ i : Fin 7, Step0601.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0600.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0600.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0600.allStagesChecked,?_,Step0600.initialMarginCheck⟩
    intro i
    rw [Step0601.inputCoefficient,← Step0600.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0601.stepData=true ∧
      (∀ i : Fin 7, Step0602.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0601.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0601.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0601.allStagesChecked,?_,Step0601.initialMarginCheck⟩
    intro i
    rw [Step0602.inputCoefficient,← Step0601.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0602.stepData=true ∧
      (∀ i : Fin 7, Step0603.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0602.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0602.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0602.allStagesChecked,?_,Step0602.initialMarginCheck⟩
    intro i
    rw [Step0603.inputCoefficient,← Step0602.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0603.stepData=true ∧
      (∀ i : Fin 7, Step0604.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0603.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0603.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0603.allStagesChecked,?_,Step0603.initialMarginCheck⟩
    intro i
    rw [Step0604.inputCoefficient,← Step0603.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0604.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0604.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0604.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0604.allStagesChecked,?_,Step0604.initialMarginCheck⟩
    intro i
    change Step0604.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0604.stepData)[i.val]
    rw [← Step0604.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0600.stepData.coefficient 0 i=Step0600.inputData[i.val]
  exact Step0600.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0600_n0050_bounded.Block0000
