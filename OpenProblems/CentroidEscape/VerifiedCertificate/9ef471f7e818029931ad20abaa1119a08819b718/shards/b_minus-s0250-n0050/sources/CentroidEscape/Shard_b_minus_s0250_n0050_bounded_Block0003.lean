import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Step0265
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Step0266
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Step0267
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Step0268
import CentroidEscape.Shard_b_minus_s0250_n0050_bounded_Step0269

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0266.inputData=Step0265.endpointData := by decide +kernel

theorem glue1 : Step0267.inputData=Step0266.endpointData := by decide +kernel

theorem glue2 : Step0268.inputData=Step0267.endpointData := by decide +kernel

theorem glue3 : Step0269.inputData=Step0268.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0265.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0269.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0265.stepData
  | 1=>Step0266.stepData
  | 2=>Step0267.stepData
  | 3=>Step0268.stepData
  | 4=>Step0269.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0265.stepData=true ∧
      (∀ i : Fin 7, Step0266.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0265.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0265.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0265.allStagesChecked,?_,Step0265.initialMarginCheck⟩
    intro i
    rw [Step0266.inputCoefficient,← Step0265.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0266.stepData=true ∧
      (∀ i : Fin 7, Step0267.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0266.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0266.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0266.allStagesChecked,?_,Step0266.initialMarginCheck⟩
    intro i
    rw [Step0267.inputCoefficient,← Step0266.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0267.stepData=true ∧
      (∀ i : Fin 7, Step0268.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0267.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0267.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0267.allStagesChecked,?_,Step0267.initialMarginCheck⟩
    intro i
    rw [Step0268.inputCoefficient,← Step0267.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0268.stepData=true ∧
      (∀ i : Fin 7, Step0269.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0268.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0268.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0268.allStagesChecked,?_,Step0268.initialMarginCheck⟩
    intro i
    rw [Step0269.inputCoefficient,← Step0268.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0269.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0269.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0269.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0269.allStagesChecked,?_,Step0269.initialMarginCheck⟩
    intro i
    change Step0269.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0269.stepData)[i.val]
    rw [← Step0269.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0265.stepData.coefficient 0 i=Step0265.inputData[i.val]
  exact Step0265.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0250_n0050_bounded.Block0003
