import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Step0135
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Step0136
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Step0137
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Step0138
import CentroidEscape.Shard_a_minus_s0100_n0050_bounded_Step0139

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0136.inputData=Step0135.endpointData := by decide +kernel

theorem glue1 : Step0137.inputData=Step0136.endpointData := by decide +kernel

theorem glue2 : Step0138.inputData=Step0137.endpointData := by decide +kernel

theorem glue3 : Step0139.inputData=Step0138.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0135.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0139.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0135.stepData
  | 1=>Step0136.stepData
  | 2=>Step0137.stepData
  | 3=>Step0138.stepData
  | 4=>Step0139.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0135.stepData=true ∧
      (∀ i : Fin 7, Step0136.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0135.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0135.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0135.allStagesChecked,?_,Step0135.initialMarginCheck⟩
    intro i
    rw [Step0136.inputCoefficient,← Step0135.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0136.stepData=true ∧
      (∀ i : Fin 7, Step0137.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0136.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0136.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0136.allStagesChecked,?_,Step0136.initialMarginCheck⟩
    intro i
    rw [Step0137.inputCoefficient,← Step0136.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0137.stepData=true ∧
      (∀ i : Fin 7, Step0138.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0137.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0137.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0137.allStagesChecked,?_,Step0137.initialMarginCheck⟩
    intro i
    rw [Step0138.inputCoefficient,← Step0137.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0138.stepData=true ∧
      (∀ i : Fin 7, Step0139.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0138.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0138.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0138.allStagesChecked,?_,Step0138.initialMarginCheck⟩
    intro i
    rw [Step0139.inputCoefficient,← Step0138.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0139.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0139.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0139.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0139.allStagesChecked,?_,Step0139.initialMarginCheck⟩
    intro i
    change Step0139.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0139.stepData)[i.val]
    rw [← Step0139.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0135.stepData.coefficient 0 i=Step0135.inputData[i.val]
  exact Step0135.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0100_n0050_bounded.Block0007
