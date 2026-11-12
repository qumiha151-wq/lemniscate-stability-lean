import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0560
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0561
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0562
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0563
import CentroidEscape.Shard_a_minus_s0550_n0050_bounded_Step0564

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Block0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0561.inputData=Step0560.endpointData := by decide +kernel

theorem glue1 : Step0562.inputData=Step0561.endpointData := by decide +kernel

theorem glue2 : Step0563.inputData=Step0562.endpointData := by decide +kernel

theorem glue3 : Step0564.inputData=Step0563.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0560.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0564.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0560.stepData
  | 1=>Step0561.stepData
  | 2=>Step0562.stepData
  | 3=>Step0563.stepData
  | 4=>Step0564.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0560.stepData=true ∧
      (∀ i : Fin 7, Step0561.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0560.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0560.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0560.allStagesChecked,?_,Step0560.initialMarginCheck⟩
    intro i
    rw [Step0561.inputCoefficient,← Step0560.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0561.stepData=true ∧
      (∀ i : Fin 7, Step0562.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0561.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0561.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0561.allStagesChecked,?_,Step0561.initialMarginCheck⟩
    intro i
    rw [Step0562.inputCoefficient,← Step0561.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0562.stepData=true ∧
      (∀ i : Fin 7, Step0563.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0562.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0562.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0562.allStagesChecked,?_,Step0562.initialMarginCheck⟩
    intro i
    rw [Step0563.inputCoefficient,← Step0562.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0563.stepData=true ∧
      (∀ i : Fin 7, Step0564.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0563.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0563.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0563.allStagesChecked,?_,Step0563.initialMarginCheck⟩
    intro i
    rw [Step0564.inputCoefficient,← Step0563.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0564.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0564.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0564.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0564.allStagesChecked,?_,Step0564.initialMarginCheck⟩
    intro i
    change Step0564.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0564.stepData)[i.val]
    rw [← Step0564.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0560.stepData.coefficient 0 i=Step0560.inputData[i.val]
  exact Step0560.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0550_n0050_bounded.Block0002
