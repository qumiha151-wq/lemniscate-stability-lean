import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0700
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0701
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0702
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0703
import CentroidEscape.Shard_a_minus_s0700_n0050_bounded_Step0704

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Block0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0701.inputData=Step0700.endpointData := by decide +kernel

theorem glue1 : Step0702.inputData=Step0701.endpointData := by decide +kernel

theorem glue2 : Step0703.inputData=Step0702.endpointData := by decide +kernel

theorem glue3 : Step0704.inputData=Step0703.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0700.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0704.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0700.stepData
  | 1=>Step0701.stepData
  | 2=>Step0702.stepData
  | 3=>Step0703.stepData
  | 4=>Step0704.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0700.stepData=true ∧
      (∀ i : Fin 7, Step0701.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0700.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0700.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0700.allStagesChecked,?_,Step0700.initialMarginCheck⟩
    intro i
    rw [Step0701.inputCoefficient,← Step0700.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0701.stepData=true ∧
      (∀ i : Fin 7, Step0702.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0701.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0701.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0701.allStagesChecked,?_,Step0701.initialMarginCheck⟩
    intro i
    rw [Step0702.inputCoefficient,← Step0701.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0702.stepData=true ∧
      (∀ i : Fin 7, Step0703.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0702.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0702.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0702.allStagesChecked,?_,Step0702.initialMarginCheck⟩
    intro i
    rw [Step0703.inputCoefficient,← Step0702.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0703.stepData=true ∧
      (∀ i : Fin 7, Step0704.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0703.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0703.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0703.allStagesChecked,?_,Step0703.initialMarginCheck⟩
    intro i
    rw [Step0704.inputCoefficient,← Step0703.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0704.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0704.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0704.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0704.allStagesChecked,?_,Step0704.initialMarginCheck⟩
    intro i
    change Step0704.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0704.stepData)[i.val]
    rw [← Step0704.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0700.stepData.coefficient 0 i=Step0700.inputData[i.val]
  exact Step0700.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0700_n0050_bounded.Block0000
