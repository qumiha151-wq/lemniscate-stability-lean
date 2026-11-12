import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Step0065
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Step0066
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Step0067
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Step0068
import CentroidEscape.Shard_a_minus_s0050_n0050_bounded_Step0069

namespace CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.Block0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0066.inputData=Step0065.endpointData := by decide +kernel

theorem glue1 : Step0067.inputData=Step0066.endpointData := by decide +kernel

theorem glue2 : Step0068.inputData=Step0067.endpointData := by decide +kernel

theorem glue3 : Step0069.inputData=Step0068.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0065.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0069.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0065.stepData
  | 1=>Step0066.stepData
  | 2=>Step0067.stepData
  | 3=>Step0068.stepData
  | 4=>Step0069.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0065.stepData=true ∧
      (∀ i : Fin 7, Step0066.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0065.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0065.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0065.allStagesChecked,?_,Step0065.initialMarginCheck⟩
    intro i
    rw [Step0066.inputCoefficient,← Step0065.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0066.stepData=true ∧
      (∀ i : Fin 7, Step0067.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0066.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0066.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0066.allStagesChecked,?_,Step0066.initialMarginCheck⟩
    intro i
    rw [Step0067.inputCoefficient,← Step0066.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0067.stepData=true ∧
      (∀ i : Fin 7, Step0068.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0067.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0067.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0067.allStagesChecked,?_,Step0067.initialMarginCheck⟩
    intro i
    rw [Step0068.inputCoefficient,← Step0067.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0068.stepData=true ∧
      (∀ i : Fin 7, Step0069.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0068.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0068.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0068.allStagesChecked,?_,Step0068.initialMarginCheck⟩
    intro i
    rw [Step0069.inputCoefficient,← Step0068.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0069.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0069.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0069.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0069.allStagesChecked,?_,Step0069.initialMarginCheck⟩
    intro i
    change Step0069.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0069.stepData)[i.val]
    rw [← Step0069.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0065.stepData.coefficient 0 i=Step0065.inputData[i.val]
  exact Step0065.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_minus_s0050_n0050_bounded.Block0003
