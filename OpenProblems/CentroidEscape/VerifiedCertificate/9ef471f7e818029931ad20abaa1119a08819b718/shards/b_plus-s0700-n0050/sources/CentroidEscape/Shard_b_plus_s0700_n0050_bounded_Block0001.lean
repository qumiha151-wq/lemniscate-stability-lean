import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0705
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0706
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0707
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0708
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Step0709

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Block0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0706.inputData=Step0705.endpointData := by decide +kernel

theorem glue1 : Step0707.inputData=Step0706.endpointData := by decide +kernel

theorem glue2 : Step0708.inputData=Step0707.endpointData := by decide +kernel

theorem glue3 : Step0709.inputData=Step0708.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0705.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0709.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0705.stepData
  | 1=>Step0706.stepData
  | 2=>Step0707.stepData
  | 3=>Step0708.stepData
  | 4=>Step0709.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0705.stepData=true ∧
      (∀ i : Fin 7, Step0706.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0705.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0705.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0705.allStagesChecked,?_,Step0705.initialMarginCheck⟩
    intro i
    rw [Step0706.inputCoefficient,← Step0705.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0706.stepData=true ∧
      (∀ i : Fin 7, Step0707.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0706.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0706.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0706.allStagesChecked,?_,Step0706.initialMarginCheck⟩
    intro i
    rw [Step0707.inputCoefficient,← Step0706.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0707.stepData=true ∧
      (∀ i : Fin 7, Step0708.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0707.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0707.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0707.allStagesChecked,?_,Step0707.initialMarginCheck⟩
    intro i
    rw [Step0708.inputCoefficient,← Step0707.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0708.stepData=true ∧
      (∀ i : Fin 7, Step0709.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0708.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0708.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0708.allStagesChecked,?_,Step0708.initialMarginCheck⟩
    intro i
    rw [Step0709.inputCoefficient,← Step0708.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0709.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0709.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0709.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0709.allStagesChecked,?_,Step0709.initialMarginCheck⟩
    intro i
    change Step0709.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0709.stepData)[i.val]
    rw [← Step0709.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0705.stepData.coefficient 0 i=Step0705.inputData[i.val]
  exact Step0705.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Block0001
