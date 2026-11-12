import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_center_s0050_n0050_bounded_Step0050
import CentroidEscape.Shard_center_s0050_n0050_bounded_Step0051
import CentroidEscape.Shard_center_s0050_n0050_bounded_Step0052
import CentroidEscape.Shard_center_s0050_n0050_bounded_Step0053
import CentroidEscape.Shard_center_s0050_n0050_bounded_Step0054

namespace CentroidEscape.CertificateShards.Shard_center_s0050_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0051.inputData=Step0050.endpointData := by decide +kernel

theorem glue1 : Step0052.inputData=Step0051.endpointData := by decide +kernel

theorem glue2 : Step0053.inputData=Step0052.endpointData := by decide +kernel

theorem glue3 : Step0054.inputData=Step0053.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0050.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0054.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0050.stepData
  | 1=>Step0051.stepData
  | 2=>Step0052.stepData
  | 3=>Step0053.stepData
  | 4=>Step0054.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0050.stepData=true ∧
      (∀ i : Fin 7, Step0051.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0050.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0050.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0050.allStagesChecked,?_,Step0050.initialMarginCheck⟩
    intro i
    rw [Step0051.inputCoefficient,← Step0050.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0051.stepData=true ∧
      (∀ i : Fin 7, Step0052.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0051.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0051.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0051.allStagesChecked,?_,Step0051.initialMarginCheck⟩
    intro i
    rw [Step0052.inputCoefficient,← Step0051.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0052.stepData=true ∧
      (∀ i : Fin 7, Step0053.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0052.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0052.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0052.allStagesChecked,?_,Step0052.initialMarginCheck⟩
    intro i
    rw [Step0053.inputCoefficient,← Step0052.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0053.stepData=true ∧
      (∀ i : Fin 7, Step0054.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0053.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0053.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0053.allStagesChecked,?_,Step0053.initialMarginCheck⟩
    intro i
    rw [Step0054.inputCoefficient,← Step0053.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0054.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0054.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0054.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0054.allStagesChecked,?_,Step0054.initialMarginCheck⟩
    intro i
    change Step0054.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0054.stepData)[i.val]
    rw [← Step0054.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0050.stepData.coefficient 0 i=Step0050.inputData[i.val]
  exact Step0050.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0050_n0050_bounded.Block0000
