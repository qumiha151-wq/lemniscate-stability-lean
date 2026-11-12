import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0610
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0611
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0612
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0613
import CentroidEscape.Shard_a_minus_s0600_n0050_bounded_Step0614

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0611.inputData=Step0610.endpointData := by decide +kernel

theorem glue1 : Step0612.inputData=Step0611.endpointData := by decide +kernel

theorem glue2 : Step0613.inputData=Step0612.endpointData := by decide +kernel

theorem glue3 : Step0614.inputData=Step0613.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0610.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0614.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0610.stepData
  | 1=>Step0611.stepData
  | 2=>Step0612.stepData
  | 3=>Step0613.stepData
  | 4=>Step0614.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0610.stepData=true ∧
      (∀ i : Fin 7, Step0611.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0610.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0610.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0610.allStagesChecked,?_,Step0610.initialMarginCheck⟩
    intro i
    rw [Step0611.inputCoefficient,← Step0610.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0611.stepData=true ∧
      (∀ i : Fin 7, Step0612.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0611.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0611.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0611.allStagesChecked,?_,Step0611.initialMarginCheck⟩
    intro i
    rw [Step0612.inputCoefficient,← Step0611.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0612.stepData=true ∧
      (∀ i : Fin 7, Step0613.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0612.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0612.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0612.allStagesChecked,?_,Step0612.initialMarginCheck⟩
    intro i
    rw [Step0613.inputCoefficient,← Step0612.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0613.stepData=true ∧
      (∀ i : Fin 7, Step0614.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0613.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0613.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0613.allStagesChecked,?_,Step0613.initialMarginCheck⟩
    intro i
    rw [Step0614.inputCoefficient,← Step0613.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0614.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0614.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0614.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0614.allStagesChecked,?_,Step0614.initialMarginCheck⟩
    intro i
    change Step0614.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0614.stepData)[i.val]
    rw [← Step0614.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0610.stepData.coefficient 0 i=Step0610.inputData[i.val]
  exact Step0610.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0600_n0050_bounded.Block0002
