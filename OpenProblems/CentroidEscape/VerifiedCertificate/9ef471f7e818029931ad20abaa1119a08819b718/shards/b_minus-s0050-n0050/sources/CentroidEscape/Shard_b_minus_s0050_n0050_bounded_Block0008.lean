import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Step0090
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Step0091
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Step0092
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Step0093
import CentroidEscape.Shard_b_minus_s0050_n0050_bounded_Step0094

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.Block0008
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0091.inputData=Step0090.endpointData := by decide +kernel

theorem glue1 : Step0092.inputData=Step0091.endpointData := by decide +kernel

theorem glue2 : Step0093.inputData=Step0092.endpointData := by decide +kernel

theorem glue3 : Step0094.inputData=Step0093.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0090.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0094.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0090.stepData
  | 1=>Step0091.stepData
  | 2=>Step0092.stepData
  | 3=>Step0093.stepData
  | 4=>Step0094.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0090.stepData=true ∧
      (∀ i : Fin 7, Step0091.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0090.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0090.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0090.allStagesChecked,?_,Step0090.initialMarginCheck⟩
    intro i
    rw [Step0091.inputCoefficient,← Step0090.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0091.stepData=true ∧
      (∀ i : Fin 7, Step0092.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0091.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0091.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0091.allStagesChecked,?_,Step0091.initialMarginCheck⟩
    intro i
    rw [Step0092.inputCoefficient,← Step0091.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0092.stepData=true ∧
      (∀ i : Fin 7, Step0093.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0092.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0092.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0092.allStagesChecked,?_,Step0092.initialMarginCheck⟩
    intro i
    rw [Step0093.inputCoefficient,← Step0092.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0093.stepData=true ∧
      (∀ i : Fin 7, Step0094.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0093.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0093.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0093.allStagesChecked,?_,Step0093.initialMarginCheck⟩
    intro i
    rw [Step0094.inputCoefficient,← Step0093.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0094.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0094.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0094.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0094.allStagesChecked,?_,Step0094.initialMarginCheck⟩
    intro i
    change Step0094.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0094.stepData)[i.val]
    rw [← Step0094.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0090.stepData.coefficient 0 i=Step0090.inputData[i.val]
  exact Step0090.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0050_n0050_bounded.Block0008
