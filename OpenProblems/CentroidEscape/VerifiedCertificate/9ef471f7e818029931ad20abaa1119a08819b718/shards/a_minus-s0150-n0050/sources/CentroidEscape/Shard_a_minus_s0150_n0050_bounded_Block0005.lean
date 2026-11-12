import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Step0175
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Step0176
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Step0177
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Step0178
import CentroidEscape.Shard_a_minus_s0150_n0050_bounded_Step0179

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.Block0005
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0176.inputData=Step0175.endpointData := by decide +kernel

theorem glue1 : Step0177.inputData=Step0176.endpointData := by decide +kernel

theorem glue2 : Step0178.inputData=Step0177.endpointData := by decide +kernel

theorem glue3 : Step0179.inputData=Step0178.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0175.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0179.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0175.stepData
  | 1=>Step0176.stepData
  | 2=>Step0177.stepData
  | 3=>Step0178.stepData
  | 4=>Step0179.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0175.stepData=true ∧
      (∀ i : Fin 7, Step0176.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0175.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0175.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0175.allStagesChecked,?_,Step0175.initialMarginCheck⟩
    intro i
    rw [Step0176.inputCoefficient,← Step0175.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0176.stepData=true ∧
      (∀ i : Fin 7, Step0177.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0176.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0176.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0176.allStagesChecked,?_,Step0176.initialMarginCheck⟩
    intro i
    rw [Step0177.inputCoefficient,← Step0176.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0177.stepData=true ∧
      (∀ i : Fin 7, Step0178.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0177.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0177.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0177.allStagesChecked,?_,Step0177.initialMarginCheck⟩
    intro i
    rw [Step0178.inputCoefficient,← Step0177.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0178.stepData=true ∧
      (∀ i : Fin 7, Step0179.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0178.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0178.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0178.allStagesChecked,?_,Step0178.initialMarginCheck⟩
    intro i
    rw [Step0179.inputCoefficient,← Step0178.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0179.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0179.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0179.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0179.allStagesChecked,?_,Step0179.initialMarginCheck⟩
    intro i
    change Step0179.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0179.stepData)[i.val]
    rw [← Step0179.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0175.stepData.coefficient 0 i=Step0175.inputData[i.val]
  exact Step0175.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0150_n0050_bounded.Block0005
