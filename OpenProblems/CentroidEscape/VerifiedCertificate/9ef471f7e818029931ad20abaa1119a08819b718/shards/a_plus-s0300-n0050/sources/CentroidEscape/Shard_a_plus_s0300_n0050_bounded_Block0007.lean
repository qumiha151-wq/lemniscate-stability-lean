import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Step0335
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Step0336
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Step0337
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Step0338
import CentroidEscape.Shard_a_plus_s0300_n0050_bounded_Step0339

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.Block0007
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue0 : Step0336.inputData=Step0335.endpointData := by decide +kernel

theorem glue1 : Step0337.inputData=Step0336.endpointData := by decide +kernel

theorem glue2 : Step0338.inputData=Step0337.endpointData := by decide +kernel

theorem glue3 : Step0339.inputData=Step0338.endpointData := by decide +kernel

noncomputable def inputData : Vector FixedBall 7 := Step0335.inputData
noncomputable def endpointData : Vector FixedBall 7 := Step0339.endpointData
noncomputable def terminalData : FixedTaylorState := ⟨#[endpointData],#[]⟩

noncomputable def stages : ℕ → FixedTaylorState
  | 0=>Step0335.stepData
  | 1=>Step0336.stepData
  | 2=>Step0337.stepData
  | 3=>Step0338.stepData
  | 4=>Step0339.stepData
  | _=>terminalData

theorem checked : Order60SegmentValid mesh stepTime 5 stages := by
  intro j hj
  interval_cases j
  · change checkOrderTaylorData mesh 60 Step0335.stepData=true ∧
      (∀ i : Fin 7, Step0336.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0335.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0335.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0335.allStagesChecked,?_,Step0335.initialMarginCheck⟩
    intro i
    rw [Step0336.inputCoefficient,← Step0335.endpointCorrect,glue0]
  · change checkOrderTaylorData mesh 60 Step0336.stepData=true ∧
      (∀ i : Fin 7, Step0337.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0336.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0336.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0336.allStagesChecked,?_,Step0336.initialMarginCheck⟩
    intro i
    rw [Step0337.inputCoefficient,← Step0336.endpointCorrect,glue1]
  · change checkOrderTaylorData mesh 60 Step0337.stepData=true ∧
      (∀ i : Fin 7, Step0338.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0337.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0337.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0337.allStagesChecked,?_,Step0337.initialMarginCheck⟩
    intro i
    rw [Step0338.inputCoefficient,← Step0337.endpointCorrect,glue2]
  · change checkOrderTaylorData mesh 60 Step0338.stepData=true ∧
      (∀ i : Fin 7, Step0339.stepData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0338.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0338.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0338.allStagesChecked,?_,Step0338.initialMarginCheck⟩
    intro i
    rw [Step0339.inputCoefficient,← Step0338.endpointCorrect,glue3]
  · change checkOrderTaylorData mesh 60 Step0339.stepData=true ∧
      (∀ i : Fin 7, terminalData.coefficient 0 i=
        (evaluateFixedTaylorOrder mesh 60 stepTime Step0339.stepData)[i.val]) ∧
      checkBallCanonicalMargin (fun i=>(Step0339.stepData.coefficient 0 i).toRational mesh)=true
    refine ⟨Step0339.allStagesChecked,?_,Step0339.initialMarginCheck⟩
    intro i
    change Step0339.endpointData[i.val]=(evaluateFixedTaylorOrder mesh 60 stepTime Step0339.stepData)[i.val]
    rw [← Step0339.endpointCorrect]

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change Step0335.stepData.coefficient 0 i=Step0335.inputData[i.val]
  exact Step0335.inputCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 5).coefficient 0 i=endpointData[i.val] := by rfl

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0300_n0050_bounded.Block0007
