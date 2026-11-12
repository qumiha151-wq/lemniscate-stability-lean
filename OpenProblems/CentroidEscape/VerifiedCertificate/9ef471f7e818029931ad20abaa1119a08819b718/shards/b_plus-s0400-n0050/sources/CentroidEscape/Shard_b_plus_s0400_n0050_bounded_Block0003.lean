import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0415
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0416
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0417
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0418
import CentroidEscape.Shard_b_plus_s0400_n0050_bounded_Step0419

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0416.inputData=Step0415.endpointData := by decide +kernel

theorem glue1 : Step0417.inputData=Step0416.endpointData := by decide +kernel

theorem glue2 : Step0418.inputData=Step0417.endpointData := by decide +kernel

theorem glue3 : Step0419.inputData=Step0418.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0415.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0419.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0415.stepData
  | 1=>Step0416.stepData
  | 2=>Step0417.stepData
  | 3=>Step0418.stepData
  | 4=>Step0419.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0415.stepData=true ∧
      (∀ i : Fin 7, Step0416.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0415.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0415.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0415.allStagesChecked,?_,Step0415.initialMarginCheck⟩
    intro i
    rw [Step0416.inputCoefficient,← Step0415.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0416.stepData=true ∧
      (∀ i : Fin 7, Step0417.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0416.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0416.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0416.allStagesChecked,?_,Step0416.initialMarginCheck⟩
    intro i
    rw [Step0417.inputCoefficient,← Step0416.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0417.stepData=true ∧
      (∀ i : Fin 7, Step0418.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0417.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0417.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0417.allStagesChecked,?_,Step0417.initialMarginCheck⟩
    intro i
    rw [Step0418.inputCoefficient,← Step0417.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0418.stepData=true ∧
      (∀ i : Fin 7, Step0419.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0418.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0418.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0418.allStagesChecked,?_,Step0418.initialMarginCheck⟩
    intro i
    rw [Step0419.inputCoefficient,← Step0418.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0419.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0419.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0419.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0419.allStagesChecked,?_,Step0419.initialMarginCheck⟩
    intro i
    change Step0419.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0419.stepData)[i.val]
    rw [← Step0419.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0415.stepData.coefficient 0 i=Step0415.inputData[i.val]
  exact Step0415.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0400_n0050_bounded.Block0003
