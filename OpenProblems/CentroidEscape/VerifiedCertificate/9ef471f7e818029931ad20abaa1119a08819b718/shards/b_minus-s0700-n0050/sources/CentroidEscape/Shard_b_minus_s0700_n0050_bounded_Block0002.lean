import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0710
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0711
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0712
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0713
import CentroidEscape.Shard_b_minus_s0700_n0050_bounded_Step0714

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0711.inputData=Step0710.endpointData := by decide +kernel

theorem glue1 : Step0712.inputData=Step0711.endpointData := by decide +kernel

theorem glue2 : Step0713.inputData=Step0712.endpointData := by decide +kernel

theorem glue3 : Step0714.inputData=Step0713.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0710.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0714.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0710.stepData
  | 1=>Step0711.stepData
  | 2=>Step0712.stepData
  | 3=>Step0713.stepData
  | 4=>Step0714.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0710.stepData=true ∧
      (∀ i : Fin 7, Step0711.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0710.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0710.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0710.allStagesChecked,?_,Step0710.initialMarginCheck⟩
    intro i
    rw [Step0711.inputCoefficient,← Step0710.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0711.stepData=true ∧
      (∀ i : Fin 7, Step0712.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0711.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0711.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0711.allStagesChecked,?_,Step0711.initialMarginCheck⟩
    intro i
    rw [Step0712.inputCoefficient,← Step0711.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0712.stepData=true ∧
      (∀ i : Fin 7, Step0713.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0712.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0712.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0712.allStagesChecked,?_,Step0712.initialMarginCheck⟩
    intro i
    rw [Step0713.inputCoefficient,← Step0712.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0713.stepData=true ∧
      (∀ i : Fin 7, Step0714.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0713.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0713.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0713.allStagesChecked,?_,Step0713.initialMarginCheck⟩
    intro i
    rw [Step0714.inputCoefficient,← Step0713.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0714.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0714.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0714.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0714.allStagesChecked,?_,Step0714.initialMarginCheck⟩
    intro i
    change Step0714.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0714.stepData)[i.val]
    rw [← Step0714.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0710.stepData.coefficient 0 i=Step0710.inputData[i.val]
  exact Step0710.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0700_n0050_bounded.Block0002
