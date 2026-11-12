import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0740
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0741
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0742
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0743
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0744

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0741.inputData=Step0740.endpointData := by decide +kernel

theorem glue1 : Step0742.inputData=Step0741.endpointData := by decide +kernel

theorem glue2 : Step0743.inputData=Step0742.endpointData := by decide +kernel

theorem glue3 : Step0744.inputData=Step0743.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0740.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0744.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0740.stepData
  | 1=>Step0741.stepData
  | 2=>Step0742.stepData
  | 3=>Step0743.stepData
  | 4=>Step0744.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0740.stepData=true ∧
      (∀ i : Fin 7, Step0741.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0740.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0740.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0740.allStagesChecked,?_,Step0740.initialMarginCheck⟩
    intro i
    rw [Step0741.inputCoefficient,← Step0740.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0741.stepData=true ∧
      (∀ i : Fin 7, Step0742.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0741.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0741.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0741.allStagesChecked,?_,Step0741.initialMarginCheck⟩
    intro i
    rw [Step0742.inputCoefficient,← Step0741.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0742.stepData=true ∧
      (∀ i : Fin 7, Step0743.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0742.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0742.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0742.allStagesChecked,?_,Step0742.initialMarginCheck⟩
    intro i
    rw [Step0743.inputCoefficient,← Step0742.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0743.stepData=true ∧
      (∀ i : Fin 7, Step0744.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0743.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0743.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0743.allStagesChecked,?_,Step0743.initialMarginCheck⟩
    intro i
    rw [Step0744.inputCoefficient,← Step0743.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0744.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0744.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0744.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0744.allStagesChecked,?_,Step0744.initialMarginCheck⟩
    intro i
    change Step0744.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0744.stepData)[i.val]
    rw [← Step0744.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0740.stepData.coefficient 0 i=Step0740.inputData[i.val]
  exact Step0740.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Block0008
