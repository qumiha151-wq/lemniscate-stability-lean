import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0665
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0666
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0667
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0668
import CentroidEscape.Shard_a_minus_s0650_n0050_bounded_Step0669

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0666.inputData=Step0665.endpointData := by decide +kernel

theorem glue1 : Step0667.inputData=Step0666.endpointData := by decide +kernel

theorem glue2 : Step0668.inputData=Step0667.endpointData := by decide +kernel

theorem glue3 : Step0669.inputData=Step0668.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0665.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0669.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0665.stepData
  | 1=>Step0666.stepData
  | 2=>Step0667.stepData
  | 3=>Step0668.stepData
  | 4=>Step0669.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0665.stepData=true ∧
      (∀ i : Fin 7, Step0666.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0665.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0665.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0665.allStagesChecked,?_,Step0665.initialMarginCheck⟩
    intro i
    rw [Step0666.inputCoefficient,← Step0665.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0666.stepData=true ∧
      (∀ i : Fin 7, Step0667.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0666.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0666.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0666.allStagesChecked,?_,Step0666.initialMarginCheck⟩
    intro i
    rw [Step0667.inputCoefficient,← Step0666.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0667.stepData=true ∧
      (∀ i : Fin 7, Step0668.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0667.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0667.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0667.allStagesChecked,?_,Step0667.initialMarginCheck⟩
    intro i
    rw [Step0668.inputCoefficient,← Step0667.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0668.stepData=true ∧
      (∀ i : Fin 7, Step0669.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0668.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0668.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0668.allStagesChecked,?_,Step0668.initialMarginCheck⟩
    intro i
    rw [Step0669.inputCoefficient,← Step0668.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0669.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0669.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0669.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0669.allStagesChecked,?_,Step0669.initialMarginCheck⟩
    intro i
    change Step0669.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0669.stepData)[i.val]
    rw [← Step0669.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0665.stepData.coefficient 0 i=Step0665.inputData[i.val]
  exact Step0665.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0650_n0050_bounded.Block0003
