import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Step0195
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Step0196
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Step0197
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Step0198
import CentroidEscape.Shard_b_minus_s0150_n0050_bounded_Step0199

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.Block0009
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0196.inputData=Step0195.endpointData := by decide +kernel

theorem glue1 : Step0197.inputData=Step0196.endpointData := by decide +kernel

theorem glue2 : Step0198.inputData=Step0197.endpointData := by decide +kernel

theorem glue3 : Step0199.inputData=Step0198.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0195.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0199.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0195.stepData
  | 1=>Step0196.stepData
  | 2=>Step0197.stepData
  | 3=>Step0198.stepData
  | 4=>Step0199.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0195.stepData=true ∧
      (∀ i : Fin 7, Step0196.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0195.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0195.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0195.allStagesChecked,?_,Step0195.initialMarginCheck⟩
    intro i
    rw [Step0196.inputCoefficient,← Step0195.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0196.stepData=true ∧
      (∀ i : Fin 7, Step0197.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0196.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0196.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0196.allStagesChecked,?_,Step0196.initialMarginCheck⟩
    intro i
    rw [Step0197.inputCoefficient,← Step0196.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0197.stepData=true ∧
      (∀ i : Fin 7, Step0198.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0197.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0197.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0197.allStagesChecked,?_,Step0197.initialMarginCheck⟩
    intro i
    rw [Step0198.inputCoefficient,← Step0197.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0198.stepData=true ∧
      (∀ i : Fin 7, Step0199.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0198.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0198.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0198.allStagesChecked,?_,Step0198.initialMarginCheck⟩
    intro i
    rw [Step0199.inputCoefficient,← Step0198.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0199.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0199.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0199.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0199.allStagesChecked,?_,Step0199.initialMarginCheck⟩
    intro i
    change Step0199.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0199.stepData)[i.val]
    rw [← Step0199.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0195.stepData.coefficient 0 i=Step0195.inputData[i.val]
  exact Step0195.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0150_n0050_bounded.Block0009
