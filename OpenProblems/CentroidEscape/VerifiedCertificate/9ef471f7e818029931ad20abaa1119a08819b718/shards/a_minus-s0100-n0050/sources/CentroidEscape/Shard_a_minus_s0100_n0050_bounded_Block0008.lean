import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Step0140
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Step0141
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Step0142
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Step0143
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Step0144

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0141.inputData=Step0140.endpointData := by decide +kernel

theorem glue1 : Step0142.inputData=Step0141.endpointData := by decide +kernel

theorem glue2 : Step0143.inputData=Step0142.endpointData := by decide +kernel

theorem glue3 : Step0144.inputData=Step0143.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0140.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0144.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0140.stepData
  | 1=>Step0141.stepData
  | 2=>Step0142.stepData
  | 3=>Step0143.stepData
  | 4=>Step0144.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0140.stepData=true ∧
      (∀ i : Fin 7, Step0141.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0140.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0140.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0140.allStagesChecked,?_,Step0140.initialMarginCheck⟩
    intro i
    rw [Step0141.inputCoefficient,← Step0140.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0141.stepData=true ∧
      (∀ i : Fin 7, Step0142.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0141.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0141.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0141.allStagesChecked,?_,Step0141.initialMarginCheck⟩
    intro i
    rw [Step0142.inputCoefficient,← Step0141.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0142.stepData=true ∧
      (∀ i : Fin 7, Step0143.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0142.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0142.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0142.allStagesChecked,?_,Step0142.initialMarginCheck⟩
    intro i
    rw [Step0143.inputCoefficient,← Step0142.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0143.stepData=true ∧
      (∀ i : Fin 7, Step0144.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0143.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0143.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0143.allStagesChecked,?_,Step0143.initialMarginCheck⟩
    intro i
    rw [Step0144.inputCoefficient,← Step0143.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0144.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0144.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0144.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0144.allStagesChecked,?_,Step0144.initialMarginCheck⟩
    intro i
    change Step0144.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0144.stepData)[i.val]
    rw [← Step0144.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0140.stepData.coefficient 0 i=Step0140.inputData[i.val]
  exact Step0140.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.Block0008
