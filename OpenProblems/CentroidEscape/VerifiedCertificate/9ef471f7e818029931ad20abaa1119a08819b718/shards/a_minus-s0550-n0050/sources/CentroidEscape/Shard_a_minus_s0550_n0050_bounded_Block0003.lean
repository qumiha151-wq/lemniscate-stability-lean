import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0565
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0566
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0567
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0568
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0569

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0566.inputData=Step0565.endpointData := by decide +kernel

theorem glue1 : Step0567.inputData=Step0566.endpointData := by decide +kernel

theorem glue2 : Step0568.inputData=Step0567.endpointData := by decide +kernel

theorem glue3 : Step0569.inputData=Step0568.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0565.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0569.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0565.stepData
  | 1=>Step0566.stepData
  | 2=>Step0567.stepData
  | 3=>Step0568.stepData
  | 4=>Step0569.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0565.stepData=true ∧
      (∀ i : Fin 7, Step0566.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0565.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0565.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0565.allStagesChecked,?_,Step0565.initialMarginCheck⟩
    intro i
    rw [Step0566.inputCoefficient,← Step0565.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0566.stepData=true ∧
      (∀ i : Fin 7, Step0567.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0566.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0566.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0566.allStagesChecked,?_,Step0566.initialMarginCheck⟩
    intro i
    rw [Step0567.inputCoefficient,← Step0566.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0567.stepData=true ∧
      (∀ i : Fin 7, Step0568.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0567.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0567.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0567.allStagesChecked,?_,Step0567.initialMarginCheck⟩
    intro i
    rw [Step0568.inputCoefficient,← Step0567.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0568.stepData=true ∧
      (∀ i : Fin 7, Step0569.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0568.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0568.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0568.allStagesChecked,?_,Step0568.initialMarginCheck⟩
    intro i
    rw [Step0569.inputCoefficient,← Step0568.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0569.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0569.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0569.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0569.allStagesChecked,?_,Step0569.initialMarginCheck⟩
    intro i
    change Step0569.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0569.stepData)[i.val]
    rw [← Step0569.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0565.stepData.coefficient 0 i=Step0565.inputData[i.val]
  exact Step0565.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Block0003
